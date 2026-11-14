from pathlib import Path
import datetime, json, subprocess, sys, time
root=Path.cwd()
order=[s.strip() for s in Path('evidence/inputs/order.txt').read_text().splitlines() if s.strip()]
mode=sys.argv[1]
target='TCSlib/Cryptography/Randomness/Extraction'
seen=set()
def closure(module):
 if module in seen:return
 seen.add(module)
 for line in Path(module+'.lean').read_text().splitlines():
  if line.startswith('import '):
   for imported in line.split()[1:]:
    if imported.startswith('TCSlib.'):closure(imported.replace('.','/'))
closure(target)
if mode=='bootstrap':
 modules=[m for m in order if m in seen and m!=target]
 extras=[m for m in seen if m not in order]
 # New helper dependencies are inserted after the pinned prerequisites, before the owned file.
 for extra in sorted(extras):
  if '/Extraction/' not in extra:raise SystemExit(f'Unexpected prerequisite outside issued order: {extra}')
 modules+=sorted(extras)
 modules+=[target]
elif mode=='sweep':
 modules=order[:]
 for extra in sorted(seen-set(order),reverse=True):modules.insert(modules.index(target),extra)
else:
 modules=sys.argv[1:]
 mode='check-'+str(time.time_ns())
logdir=Path('evidence/logs')/mode
logdir.mkdir(parents=True,exist_ok=True)
Path('evidence/logs/'+mode+'-order.txt').write_text('\n'.join(modules)+'\n')
with Path('evidence/logs/'+mode+'-results.jsonl').open('a') as results:
 for idx,module in enumerate(modules):
  path=logdir/(module.replace('/','_')+'.log')
  started=datetime.datetime.now(datetime.timezone.utc).isoformat()
  print(f'{idx+1}/{len(modules)} START {module}',flush=True)
  with path.open('w') as log:
   log.write(f'START {started}\nCOMMAND /usr/bin/time -l bash scripts/lean_check_tree.sh {module}\n');log.flush()
   run=subprocess.run(['/usr/bin/time','-l','bash','scripts/lean_check_tree.sh',module],stdout=log,stderr=subprocess.STDOUT)
   ended=datetime.datetime.now(datetime.timezone.utc).isoformat()
   log.write(f'END {ended}\nEXIT {run.returncode}\n')
  results.write(json.dumps(dict(module=module,start=started,end=ended,exit=run.returncode,log=str(path)))+'\n');results.flush()
  print(f'{idx+1}/{len(modules)} END {module} exit={run.returncode}',flush=True)
  if run.returncode:
   print(path.read_text()[-12000:],flush=True)
   raise SystemExit(run.returncode)
