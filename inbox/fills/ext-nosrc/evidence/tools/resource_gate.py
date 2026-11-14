"""Host-wide Lean cap and the user-authorized dl-crh bootstrap slot reservation.
Only counts actual Lean executables, excluding shell wrappers and grep processes.
The caller starts one Lean job after this gate; each fill still has its own olean tree.
"""
from pathlib import Path
import json,re,subprocess,time

def wait_for_slot():
 previous=None
 while True:
  processes=subprocess.check_output(['ps','-ww','-axo','pid=,comm='],text=True)
  pids=[line.split(maxsplit=1)[0] for line in processes.splitlines() if len(line.split(maxsplit=1))==2 and Path(line.split(maxsplit=1)[1].strip()).name=='lean']
  commands=''
  if pids:
   outcome=subprocess.run(['ps','-ww','-p',','.join(pids),'-o','pid=,command='],text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
   commands=outcome.stdout
  config=json.loads(Path('evidence/logs/resource-reservation.json').read_text())
  dl_active=bool(re.search(r'dl[-_]crh',commands,re.I))
  reserve=config['reserved_slots'] if config['enabled'] and not dl_active else 0
  threshold=config['host_cap']-reserve
  if len(pids)<threshold:return
  state=(len(pids),reserve,dl_active)
  if state!=previous:
   print(f'WAIT host cap: {len(pids)} Lean processes; {reserve} slot reserved for dl-crh; dl-crh active={dl_active}',flush=True)
   previous=state
  time.sleep(1)
