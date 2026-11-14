"""Finish the explicitly separate final sweep; retain first-pass evidence unchanged."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time
order=Path('evidence/logs/final-sweep-order.txt').read_text().splitlines()
assert len(order)==203
print('Waiting for separate final sweep',flush=True)
while True:
 try:rows=[json.loads(s) for s in Path('evidence/logs/final-sweep-results.jsonl').read_text().splitlines()]
 except json.JSONDecodeError:
  time.sleep(5);continue
 if any(r['exit'] for r in rows):raise SystemExit('Final sweep failed; no completion claim')
 if len(rows)==203:break
 time.sleep(5)
assert [r['module'] for r in rows]==order
with Path('evidence/logs/final-admissions.log').open('x') as stream:
 rc=subprocess.call(['python3','-I','evidence/tools/check_admissions.py'],stdout=stream,stderr=subprocess.STDOUT)
assert rc==0,'Final admission comparison failed'
summary=json.loads(Path('evidence/logs/first-full-pass-validation-summary.json').read_text())
for area in ['base-r2','final','facade-base','facade-final']:
 data=json.loads((Path('evidence/rule10')/area/'seals-results.json').read_text())
 assert data['all_valid_harnesses'] and data['all_expected_error_counts']
 if area=='final':
  manifest=json.loads((Path('evidence/rule10')/area/'manifest.json').read_text())
  for row in manifest['seals']:
   assert hashlib.sha256(Path(row['source']).read_bytes()).hexdigest()==row['source_sha256']
 if area=='facade-final':
  config=json.loads((Path('evidence/rule10')/area/'init.json').read_text())
  assert hashlib.sha256(Path(config['source']).read_bytes()).hexdigest()==config['source_sha256']
admissions=json.loads(Path('evidence/logs/admissions-comparison.json').read_text())
assert admissions['pass']
summary.update({'result':'PASS','full_bootstrap_modules':203,'separate_final_sweep':True,'sweep_modules':203,'sweep_errors':0,'final_sweep_results':'evidence/logs/final-sweep-results.jsonl','admissions':{'base':admissions['base_declarations'],'final':admissions['final_declarations'],'removed':admissions['removed'],'added':admissions['added']},'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
Path('evidence/logs/final-validation-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('SEPARATE FINAL SWEEP AND ALL VALIDATION PASS',flush=True)
