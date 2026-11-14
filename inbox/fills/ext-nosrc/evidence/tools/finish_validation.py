"""Wait for the successful 203-module sweep, then run only its dependent checks.
Run only as python3 -I evidence/tools/finish_validation.py. All Lean calls are delegated to
capped per-module drivers; no timeout, Lake build, object-tree copying or parallel Lean occurs.
"""
from pathlib import Path
import datetime,json,subprocess,time,sys
order=Path('evidence/logs/sweep-order.txt').read_text().splitlines()
results=Path('evidence/logs/sweep-results.jsonl')
print('Waiting for successful complete sweep',flush=True)
while True:
 try:rows=[json.loads(s) for s in results.read_text().splitlines()]
 except json.JSONDecodeError:
  time.sleep(5);continue
 if any(r['exit'] for r in rows):raise SystemExit('Sweep failed; dependent facade checks skipped')
 if len(rows)==len(order):break
 time.sleep(5)
assert len(rows)==203 and [r['module'] for r in rows]==order
print('Complete sweep passed; starting dependent facade checks',flush=True)
commands=[]
for side in ['base','final']:
 commands.extend([
  ['python3','-I','evidence/tools/run_facade_rule10.py','census',side],
  ['python3','-I','evidence/tools/prepare_facade_rule10.py','seals',side],
  ['python3','-I','evidence/tools/run_facade_rule10.py','seals',side],
 ])
commands.append(['python3','-I','evidence/tools/check_admissions.py'])
start=int(sys.argv[2]) if len(sys.argv)==3 and sys.argv[1]=='--resume-from' else 1
assert 1<=start<=len(commands)
for index,command in enumerate(commands):
 if index+1<start:continue
 log=Path('evidence/logs')/f'finish-validation-{index+1}.log'
 if log.exists():log=Path('evidence/logs')/f'finish-validation-{index+1}-attempt-{time.time_ns()}.log'
 print('RUN '+' '.join(command),flush=True)
 with log.open('x') as stream:
  rc=subprocess.call(command,stdout=stream,stderr=subprocess.STDOUT)
 print(f'END exit={rc} log={log}',flush=True)
 if rc:
  print(log.read_text()[-12000:],flush=True)
  raise SystemExit(rc)
areas=['base-r2','final','facade-base','facade-final']
summary={}
for area in areas:
 p=Path('evidence/rule10')/area/'seals-results.json'
 data=json.loads(p.read_text())
 assert data['all_valid_harnesses'] and data['all_expected_error_counts'],area
 summary[area]=[{'label':r['label'],'rc':r['rc'],'errors':len(r['errors'])} for r in data['results']]
admissions=json.loads(Path('evidence/logs/admissions-comparison.json').read_text())
assert admissions['pass']
summary.update({'sweep_modules':len(rows),'sweep_errors':0,'admissions':{'base':admissions['base_declarations'],'final':admissions['final_declarations'],'removed':admissions['removed'],'added':admissions['added']},'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'result':'PASS'})
Path('evidence/logs/final-validation-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('FINAL VALIDATION PASS',flush=True)
