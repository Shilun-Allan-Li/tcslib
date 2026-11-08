"""Independent final source freeze; only inert copies and this review folder are written."""
from pathlib import Path
import sys,importlib.util,json,hashlib,re,difflib,collections
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4]
spec=importlib.util.spec_from_file_location('parser',ROOT/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py');P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
H=lambda s:hashlib.sha256(s.encode() if isinstance(s,str) else s).hexdigest()
def split_header(raw):
    """Balance binders; skip statement-local let assignments, including their indented by values."""
    c=P.clean(raw);stack=[];quoted=False;i=0;pending=0
    while i<len(c):
        ch=c[i]
        if quoted:
            if ch=='\\':i+=2;continue
            if ch=='"':quoted=False
        elif ch=='"':quoted=True
        elif ch in '([{⟨':stack.append(ch)
        elif ch in ')]}⟩':
            assert stack,(raw[:100],i)
            stack.pop()
        elif not stack:
            if re.match(r'(?:let|letI|have)\b',c[i:]) and (i==0 or not (c[i-1].isalnum() or c[i-1]=='_')):
                pending+=1
            if c.startswith(':=',i):
                if pending:
                    pending-=1
                    tail=c[i+2:];m=re.match(r'\s*by\b[^\n]*\n',tail)
                    if m:
                        line_start=c.rfind('\n',0,i)+1
                        indent=len(c[line_start:i])-len(c[line_start:i].lstrip())
                        j=i+2+m.end()
                        while j<len(c):
                            e=c.find('\n',j);e=len(c) if e<0 else e+1;line=c[j:e]
                            if line.strip() and len(line)-len(line.lstrip())<=indent:break
                            j=e
                        i=j;continue
                    i+=2;continue
                return raw[:i].rstrip(),':=',raw[i+2:].strip()
            if re.match(r'where\b',c[i:]) and (i==0 or c[i-1].isspace()):return raw[:i].rstrip(),'where',raw[i+5:].strip()
            if ch=='\n' and re.match(r'\n\s*\|',c[i:]):return raw[:i].rstrip(),'equations',raw[i:].strip()
        i+=1
    return raw.rstrip(),'none',''
# Header controls cover named assignments, statement lets, proof-valued lets, and nested assignments.
controls=[('theorem nested (h : P (input := x)) : True := by\n  trivial\n','True'),('private lemma body :\n    let B := existingMachine x\n    P B := by\n  exact h\n','P B'),('private lemma view :\n    let V : T := by\n      rw [shape]\n      exact t\n    P V := by\n  exact h\n','P V'),('theorem two :\n    let V : T := by\n      have h := p\n      exact t h\n    let n := f (input := x)\n    Q V n := by\n  exact z\n','Q V n')]
for text,ending in controls:
 h,d,b=split_header(text);assert h.endswith(ending) and d==':=' and b.startswith('by\n  '),(h,d,b)
P.header=lambda s:P.norm(split_header(s)[0])
def decls(text):
    result=[]
    for d in P.decls(text):
        raw=d['raw'];nextdoc=re.search(r'(?m)^/(?:--|-!)',raw)
        if nextdoc:raw=raw[:nextdoc.start()]
        raw=raw.rstrip()+'\n';head,delimiter,body=split_header(raw)
        prefix=''.join(text.splitlines(keepends=True)[:d['start']-1]);docstart=prefix.rfind('/--');docend=prefix.rfind('-/');doc=prefix[docstart:docend+2] if docstart>=0 and docend>docstart and not prefix[docend+2:].strip() else ''
        result.append(dict(d,raw=raw,doc=doc,header_raw=head,delimiter=delimiter,body=body,body_code=P.norm(P.clean(body)),code=P.norm(P.clean(raw))))
    return result

CAP=json.loads((OUT/'capture.json').read_text())
FILES=[r['path'] for r in CAP['files']]
STAGES={stage:{f:(OUT/'snapshots'/stage/(f+'.txt')).read_text() for f in FILES} for stage in ['api','producer','prior0d','prior429','current']}
DECLS={stage:{f:decls(text) for f,text in tree.items()} for stage,tree in STAGES.items()}
def compare(oldstage):
    result={};all_add=[];all_remove=[];headers=[];defs=[];roots=[]
    for f in FILES:
        oldlist=DECLS[oldstage][f];newlist=DECLS['current'][f];a={d['name']:d for d in oldlist};b={d['name']:d for d in newlist};common=set(a)&set(b);proof=[];doc=[];header=[];definition=[]
        for n in sorted(common):
            x,y=a[n],b[n]
            if x['header_raw']!=y['header_raw'] or x['private']!=y['private'] or x['kind']!=y['kind']:
                header.append({'name':n,'private':y['private'],'before':x['header_raw'],'after':y['header_raw']});headers.append((f,n,y['private']))
            if x['body_code']!=y['body_code']:
                row={'name':n,'private':y['private'],'kind':y['kind'],'line':y['start'],'end':y['end'],'before_body_sha256':H(x['body']),'after_body_sha256':H(y['body'])}
                if y['kind'] in ['lemma','theorem']:proof.append(row);roots.append(dict(row,path=f,change='existing-proof'))
                else:definition.append(row);defs.append((f,n,y['private'],y['kind']))
            elif x['raw']!=y['raw'] or x['doc']!=y['doc']:doc.append({'name':n,'private':y['private'],'body_token_identical':True,'raw_changed':x['raw']!=y['raw'],'leading_doc_changed':x['doc']!=y['doc']})
        added=[d for d in newlist if d['name'] not in a];removed=[d for d in oldlist if d['name'] not in b]
        for d in added:
            all_add.append((f,d['name'],d['private'],d['kind']))
            if d['kind'] in ['lemma','theorem']:roots.append({'name':d['name'],'private':d['private'],'kind':d['kind'],'line':d['start'],'end':d['end'],'path':f,'change':'new-proof'})
        all_remove += [(f,d['name'],d['private'],d['kind']) for d in removed]
        oldkeep=[d['name'] for d in oldlist if d['name'] in common];newkeep=[d['name'] for d in newlist if d['name'] in common]
        imports=lambda s:[l for l in P.clean(s).splitlines() if l.startswith('import ')]
        attributes=lambda s:[l for l in P.clean(s).splitlines() if l.startswith('attribute ') or l.startswith('@[')]
        result[f]={'declarations_before':len(oldlist),'declarations_after':len(newlist),'public_counts':[sum(not d['private'] for d in oldlist),sum(not d['private'] for d in newlist)],'private_counts':[sum(d['private'] for d in oldlist),sum(d['private'] for d in newlist)],'added':[{'name':d['name'],'private':d['private'],'kind':d['kind']} for d in added],'removed':[{'name':d['name'],'private':d['private'],'kind':d['kind']} for d in removed],'surviving_relative_order_equal':oldkeep==newkeep,'header_changes':header,'definition_changes':definition,'proof_body_changes':proof,'doc_or_layout_only_changes':doc,'imports_before':imports(STAGES[oldstage][f]),'imports_after':imports(STAGES['current'][f]),'standalone_attributes_equal':attributes(STAGES[oldstage][f])==attributes(STAGES['current'][f])}
    return {'base_stage':oldstage,'comparisons':result,'all_added':all_add,'all_removed':all_remove,'all_header_changes':headers,'all_definition_changes':defs,'proof_roots':roots}
api=compare('api');producer=compare('producer');phase2=compare('prior0d');final=compare('prior429')
for label,comparison in [('api-to-current',api),('producer-to-current',producer),('prior0d-to-current',phase2),('prior429-to-current',final)]:
 (OUT/(label+'.json')).write_text(json.dumps(comparison,indent=2)+'\n')
(OUT/'header-controls.json').write_text(json.dumps({'passed':True,'cases':[{'input':s,'full_header':split_header(s)[0],'proof_body':split_header(s)[2]} for s,_ in controls]},indent=2)+'\n')
expected_add={'Turing.FinTM.pairMapSndTM','Turing.FinTM.pairMapSndTM_computes','Turing.FinTM.pairMapSndTM_spaceUsed'}
expected_remove=set((ROOT/'campaign/fills/mig1/inputs/retired-public-names.txt').read_text().splitlines())
assert {n for _,n,p,_ in api['all_added'] if not p}==expected_add
assert {n for _,n,p,_ in api['all_removed'] if not p}==expected_remove
assert not [(f,n) for f,n,p in api['all_header_changes'] if not p]
assert not [(f,n) for f,n,p,_ in phase2['all_added'] if not p]
assert not [(f,n) for f,n,p,_ in phase2['all_removed'] if not p]
assert not phase2['all_header_changes'] and not phase2['all_definition_changes']
assert len(phase2['all_added'])==4 and all(p and k in ['lemma','theorem'] for _,n,p,k in phase2['all_added'])
assert {n for _,n,p,_ in phase2['all_removed']}=={'Turing.FinTM.emCall_pair_not_mem','Turing.FinTM.emCall_triple_not_mem'} and all(p for _,_,p,_ in phase2['all_removed'])
assert {(Path(f).name,n) for f,n,_ in api['all_header_changes']}=={('TimeConstructible.lean','Complexity.counter_count'),('Loop.lean','Turing.FinTM.loopHost_contracts'),('Loop.lean','Turing.FinTM.loopHost_prepare')}
assert {(Path(f).name,n) for f,n,_ in producer['all_header_changes']}=={('Wrappers.lean','Turing.FinTM.timedReady_dispatch'),('Wrappers.lean','Turing.FinTM.timed_ledger')}
expected_def={('Primitives.lean','Turing.FinTM.emitterP2SmallIndex'),('Primitives.lean','Turing.FinTM.emitterP2PairIndex')}
assert {(Path(f).name,n) for f,n,_,_ in api['all_definition_changes']}==expected_def
assert {(Path(f).name,n) for f,n,_,_ in producer['all_definition_changes']}==expected_def
# Read full attribute commands and annotations, not just their first source line.
def attributes(s):
 c=P.clean(s);commands=re.findall(r'(?m)^attribute\b[^\n]*(?:\n[ \t]+\S[^\n]*)*',c);anns=[]
 for m in re.finditer(r'@\[',c):
  i=m.end();depth=1;quoted=False
  while i<len(c) and depth:
   if c[i]=='"':quoted=not quoted
   elif not quoted:
    if c[i]=='[':depth+=1
    elif c[i]==']':depth-=1
   i+=1
  assert depth==0;anns.append(c[m.start():i])
 return [P.norm(x) for x in commands+anns]
allowed_imports={('TCSlib/Complexity/TuringMachine/Simulation.lean','import Mathlib.Algebra.BigOperators.Fin'),('TCSlib/Complexity/TuringMachine/Build/Catalog.lean','import TCSlib.Complexity.TuringMachine.Build.Primitives')}
actualimports=set()
for f,r in api['comparisons'].items():
 assert r['surviving_relative_order_equal'];assert not set(r['imports_before'])-set(r['imports_after']);actualimports|={(f,x) for x in set(r['imports_after'])-set(r['imports_before'])}
 assert attributes(STAGES['api'][f])==attributes(STAGES['current'][f]),f
 assert attributes(STAGES['prior0d'][f])==attributes(STAGES['current'][f]),f
 assert phase2['comparisons'][f]['surviving_relative_order_equal']
 assert phase2['comparisons'][f]['imports_before']==phase2['comparisons'][f]['imports_after']
assert actualimports==allowed_imports
# Public source ownership and visibility agree for every surviving global public full name.
public={stage:{d['name']:(f,d) for f,ds in DECLS[stage].items() for d in ds if not d['private']} for stage in ['api','prior0d','prior429','current']}
for stage in ['api','prior0d','prior429']:
 for n in set(public[stage])&set(public['current']):
  f,a=public[stage][n];g,b=public['current'][n];assert f==g and a['header_raw']==b['header_raw'] and a['kind']==b['kind']
# Literal runtime freeze except the two approved final private inj' proof fields.
inj=[]
for n in [x[1] for x in expected_def]:
 f='TCSlib/Complexity/TuringMachine/Build/Primitives.lean';a=next(d for d in DECLS['api'][f] if d['name']==n)['raw'];b=next(d for d in DECLS['current'][f] if d['name']==n)['raw'];needle="  inj' := by";assert a.count(needle)==b.count(needle)==1;ia=a.index(needle);ib=b.index(needle);assert a[:ia]==b[:ib];assert not re.search(r'^  [A-Za-z_]\w*\s*:=',b[ib:].split('\n',1)[1],re.M);inj.append({'name':n,'only_final_inj_Prop_field_masked':True,'header_toFun_data_prefix_bytes_equal':True,'masked_sha256':H(a[:ia]+"  inj' := <proof>\n")})
# Nine original private type/data/instance moves, checked from their actual Catalog source.
oldcat={d['name']:d for d in DECLS['api']['TCSlib/Complexity/TuringMachine/Build/Catalog.lean']};moves=json.loads((ROOT/'campaign/fills/mig1/review/checkpoint05-2026-11-07/evidence-check.json').read_text())['private_moves'];mapping={r['target']:r['source'] for r in moves};mapping['Turing.FinTM.timedHeads']='Turing.FinTM.f2_condHeads'
def renamed(s):
 s=re.sub(r'\bf2_condHeads\b','timedHeads',s);s=re.sub(r'\ba2_MapState\b','FwdMapState',s);s=re.sub(r'\ba2_map([\w\']*)',r'fwdMap\1',s);s=re.sub(r'\bf2_', '',s);return P.norm(P.clean(s))
moved=[]
for f,n,private,kind in api['all_added']:
 if kind in ['lemma','theorem'] or not private:continue
 b=next(d for d in DECLS['current'][f] if d['name']==n);a=oldcat[mapping[n]];assert renamed(a['raw'])==P.norm(P.clean(b['raw']));moved.append({'source':mapping[n],'target':n,'target_home':f,'kind':kind,'code_identical_modulo_approved_rename':True})
assert len(moved)==9
# Frozen forwarding exports and machine body.
contract={d['name']:d for d in decls((ROOT/'campaign/fills/mig1/inputs/forwarding-map-contract.lean.txt').read_text())};prims={d['name']:d for d in DECLS['current']['TCSlib/Complexity/TuringMachine/Build/Primitives.lean']}
exports=[]
for n in sorted(expected_add):
 assert P.norm(contract[n]['header_raw'])==P.norm(prims[n]['header_raw']);exports.append({'name':n,'header_matches_gated_contract':True,'line':prims[n]['start']})
assert contract['Turing.FinTM.pairMapSndTM']['body_code']==prims['Turing.FinTM.pairMapSndTM']['body_code']
# All17 target admissions are filled; original RAM3 proof bodies remain literal.
targets=json.loads((ROOT/'campaign/fills/mig1/inputs/target-admissions.json').read_text());baselines=json.loads((ROOT/'campaign/fills/mig1/inputs/base-admissions.json').read_text());admissions=[]
for row in baselines:
 f,n=row['path'],row['name'];a=next(d for d in DECLS['api'][f] if d['name']==n);b=next(d for d in DECLS['current'][f] if d['name']==n);target=any(t['name']==n for t in targets);remaining=bool(re.search(r'\b(?:sorry|admit)\b',b['body_code']));assert not remaining if target else remaining and a['body']==b['body'];admissions.append({'path':f,'name':n,'target':target,'remaining_admission':remaining,'literal_header_unchanged':a['header_raw']==b['header_raw'],'residual_body_identical':None if target else a['body']==b['body']})
remaining=[{'path':f,'name':d['name'],'line':d['start']} for f in FILES for d in DECLS['current'][f] if re.search(r'\b(?:sorry|admit)\b',d['body_code'])];assert len(remaining)==3 and sum(r['target'] for r in admissions)==17
(OUT/'admissions.json').write_text(json.dumps({'targets_and_residuals':admissions,'remaining_static':remaining},indent=2)+'\n')
# Exact owner/private/root list for the parent's new native inventory.
roots=[]
for r in api['proof_roots']:
 d=next(x for x in DECLS['current'][r['path']] if x['name']==r['name'])
 roots.append(dict(r,owner=r['path'].removesuffix('.lean').replace('/','.'),source_path=r['path'],source_line=r['line'],source_body_end_line=d['start']+len(d['raw'].splitlines())-1,header_sha256=H(d['header_raw']),body_sha256=H(d['body']),body_token_sha256=H(d['body_code']),declaration_chunk_sha256=H(d['raw'])))
(OUT/'proof-roots.json').write_text(json.dumps(roots,indent=2)+'\n');(OUT/'proof-roots.tsv').write_text('name\towner\tprivate\tline\tchange\n'+''.join(f"{r['name']}\t{r['owner']}\t{str(r['private']).lower()}\t{r['line']}\t{r['change']}\n" for r in roots))
# The current read-only Git/source capture independently verifies exact final scope.
assert not final['all_added'] and not final['all_removed'] and not final['all_header_changes'] and not final['all_definition_changes']
assert [(r['path'],r['name'],r['private']) for r in final['proof_roots']]==[('TCSlib/Complexity/TuringMachine/Build/Primitives.lean','Turing.FinTM.fwdMapVirtual_run',True)]
prior_roots=json.loads((OUT.parent/'review-final-source-phase2/proof-roots.json').read_text())
key=lambda r:(r['name'],r['path'],r['owner'],r['private'],r['kind'])
assert sorted(map(key,roots))==sorted(map(key,prior_roots)) and len(roots)==144
(OUT/'root-set-equivalence.json').write_text(json.dumps({'same144names_owners_private_flags_kinds':True,'current_roots':144,'source_body_hash_method':'Exact declaration-body string returned by the balanced header reader, with outer whitespace stripped; token hash additionally normalizes comments/whitespace.','source_lines_refreshed':True,'prior_phase2_root_list_sha256':H((OUT.parent/'review-final-source-phase2/proof-roots.json').read_bytes())},indent=2)+'\n')
summary={'public_source_census':{stage:sum(not d['private'] for ds in DECLS[stage].values() for d in ds) for stage in ['api','producer','prior0d','prior429','current']},'private_source_census':{stage:sum(d['private'] for ds in DECLS[stage].values() for d in ds) for stage in ['api','producer','prior0d','prior429','current']},'public_added_API':sorted(expected_add),'public_removed_API':sorted(expected_remove),'public_delta_prior0d':0,'all_surviving_public_headers_homes_visibility_kind_order_frozen':True,'private_header_changes_API':api['all_header_changes'],'private_header_changes_producer':producer['all_header_changes'],'private_header_changes_phase2':phase2['all_header_changes'],'phase2_added_private_proof_helpers':phase2['all_added'],'phase2_removed_private_proof_helpers':phase2['all_removed'],'phase2_changed_existing_proof_roots':phase2['proof_roots'],'API_proof_roots':len(roots),'API_proof_root_public':sum(not r['private'] for r in roots),'API_proof_root_private':sum(r['private'] for r in roots),'phase2_proof_roots':len(phase2['proof_roots']),'original_private_runtime_moves':moved,'only_existing_runtime_differences':inj,'phase2_existing_runtime_differences':[],'all_full_attribute_commands_equal':True,'imports_only_two_preapproved_API_edges':sorted(actualimports),'forwarding_contracts':exports,'target_admissions_filled':17,'RAM_residuals_frozen':3,'final_vs429':{'authored_added':final['all_added'],'authored_removed':final['all_removed'],'header_changes':final['all_header_changes'],'definition_changes':final['all_definition_changes'],'changed_proof_roots':final['proof_roots']},'source_only':'Read-only Git/full-source comparison; no Lean/screen/source/cache/snapshot mutations. Parent owns native/replay evidence.'}
(OUT/'freeze-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['phase2_changed_existing_proof_roots','original_private_runtime_moves','forwarding_contracts']},indent=2))
