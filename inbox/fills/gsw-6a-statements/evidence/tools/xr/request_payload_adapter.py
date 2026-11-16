"""Proposed combined-head adapter with a scoped instance unfolding mask.

Uses the reviewed constant-AST encoder and lossless Name metadata. The mask
changes only unfolding membership for requested definitions in sealed probes.
"""
from pathlib import Path
import importlib.util, json, re, sys

LEGACY_PAYLOAD = Path(__file__).with_name('legacy_request_payload_adapter.py')
LEGACY_SHA = 'ae79f1ec66e93c8bc7749a53e12e3d383feda020ad2978520a0cfa24b12eb5de'
NEGATIVE_INSTANCE = '''theorem instanceBody :
    (default : Turing.Cfg 0 Bool Unit []) =
      ⟨none, 0, (fun _ _ => none), (fun _ => 0), []⟩ := rfl
'''

def need(ok, message):
    if not ok: raise RuntimeError(message)

def canonical(value): return json.dumps(value, ensure_ascii=False, separators=(',', ':'))

def name_key(identity):
    need(isinstance(identity,dict) and set(identity)=={'display','components'},'invalid actual-Name identity')
    parts=identity['components']; need(isinstance(parts,list) and parts,'anonymous/invalid actual Name')
    for tag,value in parts:
        need(tag in ('str','num') and isinstance(value,str),'invalid Name component')
        if tag=='num': need(re.fullmatch(r'0|[1-9][0-9]*',value) is not None,'noncanonical numeric component')
    return canonical(parts)

def records(log, tag):
    pattern=re.compile(r'(?:^|\b)'+re.escape(tag)+r' (\{.*\})$')
    return [json.loads(m[1]) for line in log.splitlines() if (m:=pattern.search(line))]

def catalog_and_roots(log, modules):
    begin=records(log,'G06-CATALOG-BEGIN'); end=records(log,'G06-CATALOG-END')
    need(len(begin)==len(end)==1,'missing/duplicate complete catalog markers')
    catalog={}; keys=set()
    for row in records(log,'G06-CATALOG'):
        spelling=row['name']['display']; key=name_key(row['name']); name_key(row['home'])
        need(spelling not in catalog and key not in keys,'ambiguous actual-Name spelling/components')
        need(row['home']['display'].startswith('TCSlib.'),'non-TCS catalog home')
        need(row['kind'] in {'def','theorem','opaque','axiom','quotient','inductive','constructor','recursor'},'unknown constant kind')
        need(all(isinstance(row[k],bool) for k in ('instance','matcher','abbrev')),'invalid catalog booleans')
        need(row['status'] in {'reducible','semireducible','irreducible','not_definition'},'invalid reducibility')
        catalog[spelling]=row; keys.add(key)
    need(begin[0]['count']==end[0]['count']==len(catalog),'catalog count mismatch')
    roots={m:{} for m in modules}
    for row in records(log,'G06-ROOT'):
        module=row['module']['display']; name=row['name']['display']; need(module in roots,'out-of-scope root')
        need(name in catalog and row['name']==catalog[name]['name'] and catalog[name]['home']==row['module'],'root identity/home differs')
        need(name not in roots[module] and row['kind']==catalog[name]['kind'],'duplicate/wrong-kind root')
        for field in ('type_refs','value_refs','axioms'):
            values=[name_key(n) for n in row[field]]; need(len(values)==len(set(values)),'duplicate actual reference/axiom')
        roots[module][name]=row
    for module in modules:
        expected={name for name,row in catalog.items() if row['home']['display']==module}
        need(expected and set(roots[module])==expected,'all-stored root set incomplete: '+module)
    return catalog,roots

def enrich_rows(legacy, log, modules, closures):
    terms,conservative,inventory=legacy(log,modules,closures)
    catalog,roots=catalog_and_roots(log,modules)
    for module in modules:
        # Includes ALL semireducible definition-instances; ONLY exact eval is special notation.
        expected={name for name,row in catalog.items() if row['home']['display'] in closures[module]
                  and row['kind']=='def' and (row['matcher'] or row['status']!='reducible')
                  and name!='Complexity.PolyExpr.eval'}
        need(set(conservative[module])==expected,'incomplete conservative ordinary-definition catalog: '+module)
        for group in (terms[module],conservative[module]):
            for name,row in group.items():
                meta=catalog[name]
                need(row['home']==meta['home']['display'] and row['matcher']==meta['matcher'] and
                     row['collector_reducibility']==meta['status'],'collector/catalog metadata differs')
                row.update(name_components=meta['name']['components'],home_components=meta['home']['components'],
                           instance=meta['instance'],abbrev=meta['abbrev'],constant_kind=meta['kind'])
        need(len(roots[module])==inventory[module]['stored_constants'],'ROOT/MODULE count differs')
        need({a['printed_actual_name'] for a in inventory[module]['axioms']}==set(roots[module]),'AXIOMSID/ROOT actual sets differ')
        # Status-reducible non-abbrevs remain explicit coverage observations, never ordinary-body passes.
        inventory[module].update(actual_name_components_verified=True,root_records=roots[module],
            semireducible_instance_names=sorted(n for n in expected if catalog[n]['instance'] and catalog[n]['status']=='semireducible'),
            reducible_candidates=[catalog[n] for n in sorted(catalog) if catalog[n]['kind']=='def'
                and catalog[n]['home']['display'] in closures[module] and catalog[n]['status']=='reducible'],
            unsealable_reducible_nonabbrev_names=sorted(n for n in catalog if catalog[n]['kind']=='def'
                and catalog[n]['home']['display'] in closures[module] and catalog[n]['status']=='reducible'
                and not catalog[n]['abbrev']))
    return terms,conservative,inventory

def augment(raw, rows, label, phase):
    """Retain the reviewed guards and constant-AST requests, add component identity checks."""
    matrix=[]
    for row in rows:
        matrix.append([row['spelling'],canonical(row['name_components']),canonical(row['home_components']),
                       str(row['instance']).lower(),str(row['matcher']).lower(),str(row['abbrev']).lower()])
    need(len({r[0] for r in matrix})==len(matrix),'duplicate component request')
    need(all(all(ord(c)>=32 and c not in '\t\n' for c in f) for r in matrix for f in r),'unsupported component payload')
    payload='\n'.join('\t'.join(r) for r in matrix)
    metadata='''  let rec nameParts : Lean.Name → List (String × String)
    | .anonymous => []
    | .str p s => nameParts p ++ [("str", s)]
    | .num p n => nameParts p ++ [("num", toString n)]
  let nameKey (n : Lean.Name) : String := (Lean.toJson (nameParts n)).compress
  let componentPayload : String := '''+json.dumps(payload,ensure_ascii=False)+'''
  let mut components : Std.HashMap String (String × String × String × String × String) := {}
  for line in (if componentPayload.isEmpty then [] else componentPayload.splitOn "\\n") do
    match line.splitOn "\\t" with
    | [n, nk, hk, i, m, a] =>
      if (components[n]?).isSome then throwError "G06-HARNESS {label}: duplicate component request"
      components := components.insert n (nk, hk, i, m, a)
    | _ => throwError "G06-HARNESS {label}: malformed component request"
  unless components.size == requests.size do throwError "G06-HARNESS {label}: component count differs"
'''
    needle='  let env ← Lean.getEnv\n'.encode(); need(raw.count(needle)==1,'environment anchor changed')
    raw=raw.replace(needle,metadata.encode()+needle,1)
    # Only requests (not the three independent reader loops) have ci.isDefinition guards.
    guard='    unless ci.isDefinition do throwError '
    text=raw.decode(); lines=text.splitlines(keepends=True); positions=[i for i,l in enumerate(lines) if l.startswith(guard)]
    need(len(positions)==1,'definition request guard changed')
    check='''    let some (nk, hk, ei, em, ea) := components[spelling]?
      | throwError "G06-HARNESS {label}: missing component request"
    unless nameKey n == nk && nameKey home == hk do
      throwError "G06-HARNESS {label}: actual Name components differ"
    let instanceFlag := Lean.Meta.isInstanceCore env n
    let matcherFlag := (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome
    let abbrevFlag := match ci with
      | .defnInfo d => match d.hints with | .abbrev => true | _ => false
      | _ => false
    unless toString instanceFlag == ei && toString matcherFlag == em && toString abbrevFlag == ea do
      throwError "G06-HARNESS {label}: definition/instance metadata differs"
    Lean.logInfo m!"G06-COMPONENT label={label} phase=PHASE spelling={spelling} key={nk} home_key={hk} instance={instanceFlag}"
'''.replace('PHASE',phase)
    i=positions[0]; lines.insert(i+1,check)
    return ''.join(lines).encode()

def insert_before(raw, anchor, extra):
    need(raw.count(anchor)==1,'mask insertion anchor changed')
    return raw.replace(anchor,extra.encode()+anchor,1)

def mask_seal(raw, *, end):
    """Add checks within the existing installation and EOF commands."""
    verified=b'    verified := verified + 1\n'
    if end:
        raw=insert_before(raw,verified,'''    if Lean.Meta.isGlobalInstance env n then
      throwError "G06-HARNESS {label}: unfolding membership at EOF for {spelling}"
''')
        return insert_before(raw,b'  Lean.logInfo m!"G06-SEAL-END ','''  Lean.logInfo m!"G06-MASK label={label} phase=eof requested={requests.size} verified={verified}"
''')
    raw=insert_before(raw,b'  let mut catalog : Std.HashMap String (Array Lean.Name) := {}\n',
        '  let mut resolved : Array Lean.Name := #[]\n')
    raw=insert_before(raw,verified,'    resolved := resolved.push n\n')
    return insert_before(raw,b'  Lean.logInfo m!"G06-SEAL ','''  let maskExt := Lean.Meta.globalInstanceExtension
  let maskEnv ← Lean.getEnv
  let scopes := maskExt.ext.getState maskEnv
  unless scopes.stateStack.length == 1 do
    throwError "G06-HARNESS {label}: unfolding mask requires base scope"
  let mut scopedNames : Std.HashSet Lean.Name := {}
  for (_, payloads) in scopes.scopedEntries.map.toList do
    for n in payloads do
      scopedNames := scopedNames.insert n
  let mut removed : Nat := 0
  for n in resolved do
    if scopedNames.contains n then
      throwError "G06-HARNESS {label}: scoped unfolding payload intersects request {n}"
    if Lean.Meta.isGlobalInstance maskEnv n then
      removed := removed + 1
  -- InstanceEntry's BEq checks only val, so compare every field explicitly.
  let entryFields (e : Lean.Meta.InstanceEntry) :=
    (e.keys, Lean.ExprStructEq.mk e.val, e.priority, e.globalName?, e.synthOrder, e.attrKind)
  let lookupSnapshot (e : Lean.Environment) :=
    let s := Lean.Meta.instanceExtension.getState e
    (s.discrTree.toArray.map (fun (ks, entry) => (ks, entryFields entry)),
      s.instanceNames.toArray.map (fun (n, entry) => (n, entryFields entry)), s.erased.toList)
  let beforeLookup := lookupSnapshot env
  Lean.modifyEnv fun current =>
    maskExt.modifyState current fun membership =>
      resolved.foldl (fun s n => s.erase n) membership
  let maskedEnv ← Lean.getEnv
  unless beforeLookup == lookupSnapshot maskedEnv do
    throwError "G06-HARNESS {label}: typeclass lookup state changed"
  for n in resolved do
    if Lean.Meta.isGlobalInstance maskedEnv n then
      throwError "G06-HARNESS {label}: unfolding membership after mask for {n}"
  Lean.logInfo m!"G06-MASK label={label} phase=install requested={requests.size} verified={resolved.size} removed={removed} scope_depth=1 scoped_names={scopedNames.size} tc_state=preserved"
''')

def configure_builders(bs, controls):
    import hashlib
    need(hashlib.sha256(LEGACY_PAYLOAD.read_bytes()).hexdigest()==LEGACY_SHA,'reviewed legacy payload changed')
    sys.dont_write_bytecode=True
    spec=importlib.util.spec_from_file_location('combined_reviewed_payload',LEGACY_PAYLOAD)
    legacy=importlib.util.module_from_spec(spec); spec.loader.exec_module(legacy)
    need(not getattr(bs,'combined_configured',False),'adapter configured twice')
    legacy.configure_builders(bs,controls)
    old_rows,old_seal,old_catalog=bs.collector_rows,bs.seal_command,controls.catalog_command
    bs.collector_rows=lambda log,modules,closures: enrich_rows(old_rows,log,modules,closures)
    bs.seal_command=lambda label,rows,*,end: mask_seal(
        augment(old_seal(label,rows,end=end),rows,label,'eof' if end else 'install'),end=end)
    controls.catalog_command=lambda builder,label,rows,phase: augment(old_catalog(builder,label,rows,phase),rows,label,'catalog-'+phase)
    controls.REQUIRED['Turing.instInhabitedCfg']=('TCSlib.Complexity.TuringMachine.Configuration',False)
    controls.NEGATIVE_BODIES['Instance']=('Turing.instInhabitedCfg',NEGATIVE_INSTANCE)
    bs.combined_configured=True

def verify_component_log(text,label,rows,phases):
    expected={r['spelling']:(r['name_components'],r['home_components'],r['instance']) for r in rows}
    found={p:{} for p in phases}; decode=json.JSONDecoder()
    for line in text.splitlines():
        if 'G06-COMPONENT label=' not in line: continue
        entry=line.split('G06-COMPONENT label=',1)[1]
        lab,entry=entry.split(' phase=',1); phase,entry=entry.split(' spelling=',1)
        need(lab==label and phase in found,'unexpected component-check label/phase')
        name,entry=entry.split(' key=',1); nk,end=decode.raw_decode(entry); entry=entry[end:]
        need(entry.startswith(' home_key='),'missing component home key'); entry=entry[len(' home_key='):]
        hk,end=decode.raw_decode(entry); entry=entry[end:]
        need(entry in (' instance=true',' instance=false'),'malformed component instance flag')
        need(name not in found[phase],'duplicate component validation record')
        found[phase][name]=(nk,hk,entry.endswith('true'))
    need(all(f==expected for f in found.values()),'incomplete/different component validation record set')

def verify_mask_log(text,label,rows,phases):
    count=len(rows); found=[]
    prefix=f'label={label} phase='
    for line in text.splitlines():
        if 'G06-MASK ' not in line: continue
        entry=line.split('G06-MASK ',1)[1]
        need(entry.startswith(prefix),'unexpected mask label')
        phase,sep,fields=entry[len(prefix):].partition(' ')
        need(sep and phase in ('install','eof'),'invalid mask phase')
        counts=f'requested={count} verified={count}'
        if phase=='install':
            match=re.fullmatch(re.escape(counts)+
                r' removed=(0|[1-9][0-9]*) scope_depth=1 scoped_names=(?:0|[1-9][0-9]*) tc_state=preserved',fields)
            need(match is not None and int(match[1])<=count,'invalid mask installation evidence')
        else:
            need(fields==counts,'invalid mask EOF evidence')
        found.append(phase)
    need(tuple(found)==tuple(phases),'incomplete/extra/out-of-order mask evidence')
