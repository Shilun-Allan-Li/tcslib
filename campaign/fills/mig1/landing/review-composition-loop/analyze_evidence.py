"""Summarize retained receipts; reject incomplete controls and unaccounted foreign definitions."""
from pathlib import Path
from collections import Counter,defaultdict
import hashlib
import json
import re

out=Path(__file__).resolve().parent
log=(out/'metadata-current.out').read_text();lines=log.splitlines()
def attrs(parts): return dict(x.split('=',1) for x in parts)
census=[];targets=[];aux=[];defs=[];simp=[]
for line in lines:
    a=line.split('|')
    if a[0]=='CENSUS':census.append(dict(name=a[1],owner=a[2],**attrs(a[3:])))
    elif a[0]=='TARGET':targets.append(dict(name=a[1],owner=a[2],**attrs(a[3:])))
    elif a[0]=='AUXILIARY':aux.append(dict(name=a[1],owner=a[2],**attrs(a[3:])))
    elif a[0]=='DEF':defs.append(dict(consumer=a[1],name=a[2],owner=a[3],**attrs(a[4:])))
    elif a[0]=='SIMPDEF':simp.append(dict(name=a[1],owner=a[2],**attrs(a[3:])))
assert len(census)==len({r['name'] for r in census})==809
assert len(targets)==40 and len(aux)==56
byname={r['name']:r for r in census}
axrows=re.findall(r'(?m)^AXIOMS\|([^|\n]+)\|\[([^]]*)\]',log)
axioms={n:[x.strip() for x in value.split(',') if x.strip()] for n,value in axrows}
assert set(axioms)=={r['name'] for r in targets+aux} and len(axioms)==96
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(ax)<=allowed for ax in axioms.values())
assert all(r['simp']=='false' and r['unfold']=='false' for r in targets)
common=json.loads((out/'Composition-new-seal-v1.coverage.json').read_text())['sealed_definitions']
loop=json.loads((out/'Loop-new-seal-v10.coverage.json').read_text())['sealed_definitions']
wrapper=next(l for l in (out/'Wrappers-new-seal-v2.lean.txt').read_text().splitlines() if l.startswith('attribute [local irreducible]')).split('] ',1)[1].split()
sets={'TCSlib.Complexity.TuringMachine.Composition':set(common),
'TCSlib.Complexity.TuringMachine.Build.Wrappers':set(wrapper),
'TCSlib.Complexity.TuringMachine.Build.Loop':set(loop)}
foreign={};regular_byhome=defaultdict(set)
matcher='Turing.FinTM.rewind_scan.match_1'
for row in defs:
    if row['sameOwner']!='false':continue
    foreign[row['name']]=dict(name=row['name'],owner=row['owner'],hints=row['hints'])
    if row['hints']=='regular':
        home=byname[row['consumer']]['owner'];regular_byhome[home].add(row['name'])
        assert row['name'] in sets[home],('unsealed direct regular definition',home,row)
assert len(foreign)==39
regular=[r for r in foreign.values() if r['hints']=='regular'];abbrev=[r for r in foreign.values() if r['hints']=='abbrev']
assert len(regular)==24 and len(abbrev)==15
rejections=(out/'abbrev-rejections.out').read_text()
refused=re.findall(r'failed to set `\[local irreducible\]`, `([^`]+)` is currently',rejections)
assert len(refused)==len(set(refused))==14
assert set(refused)=={r['name'] for r in abbrev}-{matcher}
assert json.loads((out/'abbrev-rejections.json').read_text())['errors']==14
for row in foreign.values():
    row['classification']='effective controlled seal' if row['hints']=='regular' else ('generated matcher: attribute ineffective, separately tested' if row['name']==matcher else 'reducible projection or Halted abbreviation: default validation refuses attribute')
constructor_expected={(tag,mode) for tag in ['none','some_false','some_true'] for mode in ['point','equation']}
matcher_controls={}
for mode in ['unsealed','sealed']:
    text=(out/('matcher-constructors-'+mode+'.out')).read_text()
    rows=[l.split('|') for l in text.splitlines() if l.startswith('MATCHERCONTROL|')]
    assert Counter((r[1],r[2]) for r in rows)==Counter({x:1 for x in constructor_expected})
    assert all(r[3]=='PASS' and r[4].startswith('kernelChecked=') for r in rows)
    receipt=json.loads((out/('matcher-constructors-'+mode+'.json')).read_text())
    assert receipt['exit']==receipt['errors']==0
    matcher_controls[mode]=dict(cases=len(rows),all_kernel_checked=True,metadata=next(l for l in text.splitlines() if l.startswith('MATCHERMETA|')))
variable=(out/'matcher-controls-unsealed.out').read_text()
assert variable.count('CONTROL|'+matcher+'|')==4 # INFO plus ERROR identity each for the two modes.
assert json.loads((out/'matcher-controls-unsealed.json').read_text())['errors']==2
usage=[l for l in (out/'matcher-usage.out').read_text().splitlines() if l.startswith('MATCHERUSE|')]
assert len(usage)==2 and all('|inType=false|inValue=true|root=true|auxiliary=false' in l for l in usage)
assert {r['name'] for r in simp}=={'Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg'}
# A lexical argument inventory complements, but does not replace, source reading or seals.
roots=json.loads((out/'metadata-roots.json').read_text());sources=json.loads((out/'source-review.json').read_text())
commands=[];unfolds=[]
for home,names in roots.items():
    source=Path(sources[home]['path']).read_text()
    for name in names:
        m=re.search(r'(?m)^(?:private )?(?:lemma|theorem|def) '+re.escape(name)+r'(?=\s|\{|\()',source)
        assert m,name
        end=source.find('\n/--',m.end());end=len(source) if end<0 else end
        block=source[m.start():end]
        # These reviewed blocks have no nested proof strings or block comments.
        clean=re.sub(r'--[^\n]*','',block)
        for t in re.finditer(r'\b(simp(?:_all|a)?|dsimp|rw|erw|unfold|change|show)\b',clean):
            offset=t.end();tail=clean[offset:];kind=t.group(1)
            if kind=='unfold':
                raw=tail.split('\n',1)[0].strip();unfolds.append(dict(home=home,root=name,arguments=raw))
            elif kind in ('change','show'):
                raw=tail.split('\n',1)[0].strip()
            else:
                ws=re.match(r'\s*(?:only\s*)?\[',tail)
                if not ws:continue
                a=offset+ws.end();j=a;depth=1
                while j<len(clean) and depth:
                    if clean[j]=='[':depth+=1
                    elif clean[j]==']':depth-=1
                    j+=1
                assert depth==0,(name,kind)
                raw=clean[a:j-1].strip()
            commands.append(dict(home=home,root=name,kind=kind,arguments=raw))
for c in commands:
    if c['kind'] in ('change','show'):continue
    # Detect a bare imported operational definition, not a definition occurring in a lemma type.
    for arg in c['arguments'].split(','):
        arg=arg.strip().removeprefix('←').strip()
        if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_\'.]*',arg):
            for n in sets['TCSlib.Complexity.TuringMachine.'+('Build.' if c['home']!='Composition' else '')+c['home']]:
                if arg==n or arg==n.removeprefix('Turing.') or arg==n.removeprefix('Turing.FinTM.'):
                    raise AssertionError(('bare foreign definition argument',c,n))
summary=dict(census_constants=len(census),roots=len(targets),compiler_descendants=len(aux),axiom_walks=len(axioms),
    axiom_classes={' '.join(k):v for k,v in Counter(tuple(v) for v in axioms.values()).items()},
    no_sorry_or_nonstandard_axioms=True,all_roots_non_simp=True,
    census_by_module={home:dict(Counter(r['kind'] for r in census if r['owner']==home)) for home in sets},
    private_constants=sum(r['private']=='true' for r in census),internal_constants=sum(r['internal']=='true' for r in census),
    direct_foreign_regular_definitions=len(regular),direct_foreign_regular_by_owner={k:sorted(v) for k,v in regular_byhome.items()},
    all_direct_foreign_regular_definitions_controlled_in_their_owner_scope=True,
    effective_control_definitions=30,confirmed_reducible_exclusions=sorted(refused),
    ineffective_matcher_attribute=dict(name=matcher,constructor_controls=matcher_controls,raw_delta_controls_fail_already_unsealed=True,covered_usage=usage),
    actual_default_simp_definitions=simp,
    direct_foreign_source_homes=sorted({r['owner'].replace('.','/')+'.lean' for r in foreign.values()}),
    lexical_command_inventory=len(commands),bare_foreign_definition_arguments_found=0,
    command_scanner_limitation='Lexical aide; manual reading and actual strong source-region elaborations govern proof semantics.')
(out/'census-current.json').write_text(json.dumps(sorted(census,key=lambda r:(r['owner'],r['name'])),indent=2)+'\n')
(out/'axioms-current.json').write_text(json.dumps(axioms,indent=2)+'\n')
(out/'foreign-inventory.json').write_text(json.dumps(sorted(foreign.values(),key=lambda r:r['name']),indent=2)+'\n')
(out/'command-arguments.json').write_text(json.dumps(commands,indent=2)+'\n')
(out/'metadata-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
md='# Inspected proof command arguments\n\nThis raw lexical index supports the source review; it is not a Lean parser. Public-reader applications, same-home definitions and local let views are distinguished during review. Core Fin index equalities in `show ... from rfl` supply equality proofs to `rw`; a Core definition is never passed directly to the rewriter. The generated rewind matcher is never named in the landing source.\n'
for home in roots:
    for name in roots[home]:
        rows=[c for c in commands if c['home']==home and c['root']==name]
        if not rows:continue
        md+='\n## '+home+'.'+name+'\n\n```lean\n'
        md+='\n'.join(r['kind']+' '+r['arguments'] for r in rows)+'\n```\n'
(out/'command-arguments.md').write_text(md)
print(json.dumps(summary,indent=2))
