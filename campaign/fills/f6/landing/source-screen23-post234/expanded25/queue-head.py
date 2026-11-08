from pathlib import Path
import datetime,hashlib,json,subprocess,sys,time
OUT=Path(__file__).resolve().parent
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
print('HEAD25 queued; waiting for actual BASE25 exit0 and released lock.',flush=True)
while not (OUT/'base-run.json').exists():time.sleep(2)
base=json.loads((OUT/'base-run.json').read_text());assert base['exit']==0 and base['full_population']==25 and base['fresh_execution']
while True:
 events=[json.loads(x) for x in (OUT/'lock-events.jsonl').read_text().splitlines()]
 if any(x['side']=='base' and x['event']=='released' for x in events):break
 time.sleep(1)
assert not (OUT/'head.out').exists() and not (OUT/'head-run.json').exists()
row=dict(utc=now(),base_receipt_sha256=hashlib.sha256((OUT/'base-run.json').read_bytes()).hexdigest(),head_capture_sha256=hashlib.sha256((OUT/'head-capture.json').read_bytes()).hexdigest(),command=['python3','-I',str(OUT/'run-side.py'),'head'],base_actual_exit=0,base_released_before_HEAD_command=True)
(OUT/'head-queue-release.json').write_text(json.dumps(row,indent=2)+'\n');print('BASE25 actual exit0 + lock release verified; invoking HEAD25 at '+row['utc'],flush=True)
q=subprocess.run(row['command']);print('HEAD25 runner exit '+str(q.returncode)+' '+now(),flush=True);sys.exit(q.returncode)
