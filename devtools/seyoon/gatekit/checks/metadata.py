from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).parent
import os as _os, json as _json
_GATE = Path(_os.environ['GATE']); _CFG = _json.loads((_GATE/'gate.json').read_text())
_REPO = Path(_CFG['repo']); _KIT = Path(__file__).resolve().parents[1]
r3 = _GATE/'replay/runtime'  # toolchain and packages of this gate's replay
w = _REPO
tools = w/'devtools/seyoon'
freeze, candidate, overlay, out = map(Path, sys.argv[1:5])
mode = sys.argv[5]
out.mkdir()
rt = out/'runtime'
rt.mkdir()
(rt/'lean-toolchain').write_bytes((r3/'lean-toolchain').read_bytes())
(rt/'.lake').mkdir()
(rt/'.lake/packages').symlink_to((r3/'.lake/packages').resolve(),target_is_directory=True)
scope = {'root':root,'tools':tools,'Path':Path}
driver = (root/'seals.py').read_text()
exec(compile(driver[driver.index('decl = '):driver.index('rows = []')],
    'seals definitions', 'exec'),scope)
focus, chunks = scope['focus'],scope['names']['chunks']
proofs = []
imports = []
for o in json.loads(freeze.read_text())['owner_source']:
    rel=o['path']
    if mode == 'two' and rel not in focus:
        continue
    src = candidate/rel
    if not src.is_file():
        src = r3/rel
    text = src.read_text()
    assert hashlib.sha256(text.encode()).hexdigest()==o['sha256']
    required = set(o['total_changed_or_added_from_campaign'])
    required.update('Turing.FinTM.'+n for n in focus.get(rel,()))
    mod = rel[:-5].replace('/','.')
    for name,_,chunk in chunks(text):
        if name not in required:
            continue
        body = chunk.split('-/',1)[1].lstrip() if chunk.startswith('/--') else chunk
        if re.match(r'(?:(?:private|protected|noncomputable)\s+)*(lemma|theorem)\s+',body):
            proofs.append((name,mod))
    imports.append(mod)
assert len(set(proofs))==len(proofs)>0
template = (_KIT/'templates/MetadataBody.lean.txt').read_text()
declaration_names='['+', '.join(f'({chr(96)}{n}, {chr(96)}{m})' for n,m in proofs)+']'
start = template.index('  let target :=')
end = template.index('  for root in roots do', start)
template=template[:start]+f"""  let targets : List (Name × Name) := {declaration_names}
  let table := env.constants.toList
  let roots := table.filterMap fun (n, _) =>
    if targets.contains ((privateToUserName? n).getD n, homeOf n) then some n else none
  unless roots.length == targets.length do
    throwError "selected count {{roots.length}} for {{targets.length}}"
"""+template[end:]
template=template.replace('let nameHits := env.constants.toList.filter','let nameHits := table.filter')
template=template.replace('("name",toJson root.toString),("owner",toJson owner.toString),',
    '("name",toJson root.toString),("surface",toJson (((privateToUserName? root).getD root).toString)),("owner",toJson owner.toString),')
template=template.replace('("root",toJson root.toString),("owner",toJson owner.toString),',
    '("root",toJson root.toString),("surface",toJson (((privateToUserName? root).getD root).toString)),("owner",toJson owner.toString),')
# Repeated large rendered foreign values are unnecessary to derive the boundary.
a=template.index('    for n in ordinary do')
b=template.index('  logInfo m!"COMPLETE|',a)
template=template[:a]+template[b:]
code='import Lean\n'+''.join(f'import {i}\n' for i in sorted(set(imports)))+template
f=rt/'Metadata.lean'
f.write_text(code)
cmd=['bash',str(tools/'leanelab.sh'),str(rt),str(overlay),f.name]
p=subprocess.run(cmd,capture_output=True)
log=p.stdout+p.stderr
(out/'Metadata.log').write_bytes(log)
assert p.returncode==0 and b'error:' not in log, (p.returncode,log[-6000:])
result={x:{} for x in ('SELECTED','BOUNDARY')}
for line in log.decode().splitlines():
    for label,table in result.items():
        if label+'|' in line:
            row=json.loads(line.split(label+'|',1)[1]);key=row['surface']
            assert key not in table
            table[key]=row
assert set(result['SELECTED'])==set(result['BOUNDARY'])=={n for n,_ in proofs}
for n,mod in proofs:
    row=result['SELECTED'][n]
    assert row['kind']=='theorem' and row['owner']==mod and row['typeIsProp']
    assert not set(row['axioms'])-{'propext','Quot.sound','Classical.choice'},(n,row['axioms'])
for name in ('Turing.FinTM.controlAction_def', 'Turing.inputMoveAction_eq', 'Turing.inputFoldTM_tr_bwd',
             'Turing.Cfg.ofWords_mapState'):
    if name in result['SELECTED']:
        r=result['SELECTED'][name]
        assert not r['simp'] and not r['unfold'],(name,r['simp'],r['unfold'])
        if name!='Turing.Cfg.ofWords_mapState':
            assert not r['axioms'],(name,r['axioms'])
for row in result['BOUNDARY'].values():
    assert sorted(d['name'] for d in row['foreign_definitions'] if d['ordinary'])==sorted(row['ordinary_foreign_heads'])
(out/'DATA.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
summary={'pass':True,'proofs':len(proofs),'source':str(candidate),'objects':str(overlay),
    'argv':cmd,'log_sha256':hashlib.sha256(log).hexdigest(),
    'ordinary_heads':sorted({n for row in result['BOUNDARY'].values() for n in row['ordinary_foreign_heads']}),
    'selected_axioms_standard':True}
(out/'RESULT.json').write_text(json.dumps(summary,indent=2)+'\n')
print('COMPILED DEFINITION BOUNDARIES',len(proofs),'proofs',len(summary['ordinary_heads']),'heads',flush=True)
