# io-sprg partial paired-control verification, Mac host 2026-11-18. No Lean.
# Filters only completed runs bound to the current job-owned import environment.
import json,runpy,subprocess
from pathlib import Path
root=Path.cwd();r=root/'evidence/rule10/m0_final';bind=runpy.run_path(str(root/'evidence/tools/io-sprg-rule10/environment_binding.py'));env=bind['snapshot'](root/'.lake/io-sprg-oleans',r)
latest={}
for line in(r/'control-runs/results.jsonl').read_text().splitlines():
 row=json.loads(line)
 if 'module' in row:latest[row['module']]=row
plans=[]
for variant in ['coe-A','coe-B','strict-A','strict-B']:
 for plan in json.loads((r/'controls'/variant/'controls-plan.json').read_text()):
  b=bind['previous'](r/'control-environment-bindings.jsonl',plan['module']);row=latest.get(plan['module'])
  if b and row and b['environment_sha256']==env and b['source_sha256']==row['source_sha256']==plan['source_sha256'] and b['log_sha256']==row['log_sha256']:plans.append(plan)
assert plans
(r/'control-progress-plan.json').write_text(json.dumps(plans,indent=1)+'\n')
with(r/'control-progress-check.log').open('w') as out:subprocess.run(['python3','-I',str(root/'evidence/tools/seal/review/ctlcheck2.py'),str(r/'control-progress-plan.json'),str(r/'control-runs'),str(r/'control-progress-check.json')],stdout=out,stderr=subprocess.STDOUT,check=True)
result=json.loads((r/'control-progress-check.json').read_text());assert result['all_ok']
print('PER_CONTROL_PROGRESS_ALL_OK',len(plans),'probes;',sum(len(p['controls']) for p in plans),'individual controls')
