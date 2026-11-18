# io-sprg one-step evidence finalizer. No Lean; bind a current or archived checked source.
import argparse,hashlib,json,re,runpy
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('number',type=int);ap.add_argument('build');a=ap.parse_args()
root=Path.cwd();p=root/'evidence/steps'/f'{a.number:03d}'/'step.json';record=json.loads(p.read_text())
rows=[json.loads(l) for l in(root/a.build/'results.jsonl').read_text().splitlines()]
matching=[r for r in rows if r.get('module','')+'.lean'==record['file']]
assert matching, 'No checked owner record for this proof step'
r=matching[-1]
assert r['rc']==r['errors']==r['error_forms']==0
assert r['module']+'.lean'==record['file']
candidates=[root/record['file']]+list((root/'evidence/steps').glob('*/before.lean.txt'))
binding=next((q for q in candidates if hashlib.sha256(q.read_bytes()).hexdigest()==r['source_sha256']),None)
assert binding is not None,'Checked source not available in current tree or archived steps'
record.update(status='CHECKED_PASS',checked_source_sha256=r['source_sha256'],checked_source_copy=str(binding.relative_to(root)),check=str(Path(a.build)/'results.jsonl'))
p.write_text(json.dumps(record,indent=1)+'\n')
strip=runpy.run_path(str(root/'evidence/tools/clash/clash_scan.py'))['strip_code']
holes=0
for q in(root/'TCSlib/Cryptography/Obfuscation').rglob('*.lean'):
    code='\n'.join(strip(q.read_text()))
    holes+=len(re.findall(r'\bsorry\b',code))
with(root/'evidence/lean_proof/OUTLINE.md').open('a') as out:
    out.write(f'\nStep {a.number:03d}: {record["name"]} owner check passed. Current sorry tokens: {holes}.\n')
print('STEP_CHECKED',a.number,record['name'],'current_sorry_tokens',holes)
