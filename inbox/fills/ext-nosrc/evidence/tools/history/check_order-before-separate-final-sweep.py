from pathlib import Path
import datetime, json, subprocess, sys, time, runpy
root=Path.cwd()
order=[s.strip() for s in Path('evidence/inputs/order.txt').read_text().splitlines() if s.strip()]
arguments=[x for x in sys.argv[1:] if x!='--resume']
resume='--resume' in sys.argv[1:]
mode=arguments[0]
wait_for_slot=runpy.run_path('evidence/tools/resource_gate.py')['wait_for_slot']
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
elif mode=='prerequisites':
 closure('TCSlib/Cryptography/Randomness/Extraction/Sampler')
 modules=[m for m in order if m in seen and m!=target and not Path('.lake/tcslib-check-oleans',m+'.olean').exists()]
 modules += [m for m in sorted(seen-set(order)) if not Path('.lake/tcslib-check-oleans',m+'.olean').exists()]
elif mode=='sweep':
 allowed=set(order)|seen
 modules=[]
 scheduled=set()
 def visit(module):
  if module in scheduled:return
  for line in Path(module+'.lean').read_text().splitlines():
   if line.startswith('import '):
    for imported in line.split()[1:]:
     if imported.startswith('TCSlib.'):
      dep=imported.replace('.','/')
      if dep not in allowed:raise SystemExit('Import outside issued order and owned helper closure: '+dep)
      visit(dep)
  scheduled.add(module);modules.append(module)
 for module in order:visit(module)
else:
 modules=arguments
 mode='check-'+str(time.time_ns())
logdir=Path('evidence/logs')/mode
logdir.mkdir(parents=True,exist_ok=True)
Path('evidence/logs/'+mode+'-order.txt').write_text('\n'.join(modules)+'\n')
result_path=Path('evidence/logs/'+mode+'-results.jsonl')
completed=[]
if resume:
 completed=[json.loads(line) for line in result_path.read_text().splitlines()]
 assert [r['module'] for r in completed]==modules[:len(completed)]
 assert all(r['exit']==0 for r in completed)
 for result in completed:
  assert Path(result['log']).is_file()
 print(f'RESUME verified completed prefix: {len(completed)} modules',flush=True)
with result_path.open('a') as results:
 for idx,module in enumerate(modules):
  if idx<len(completed):continue
  path=logdir/(module.replace('/','_')+'.log')
  if path.exists():path=logdir/(module.replace('/','_')+'-attempt-'+str(time.time_ns())+'.log')
  wait_for_slot()
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
