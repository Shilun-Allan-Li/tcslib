# io-sprg host-slot evidence extractor, Mac host 2026-11-18. Read-only source.
# Copies only tag=io-sprg lines; no other job's command text is delivered.
import argparse,datetime,hashlib,json,re
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--require-closed',action='store_true');a=ap.parse_args()
src=Path('/Users/seyoonr/.lean-slots/slots.log');out=Path('evidence/host');out.mkdir(exist_ok=True)
lines=[l for l in src.read_text().splitlines() if ' tag=io-sprg ' in l];assert lines
active={};events=[];max_wrappers=0;count3=0
for line in lines:
 m=re.match(r'(\S+) (\S+) pid=(\d+) tag=io-sprg (.*)',line);assert m,line
 stamp,kind,pid,rest=m.groups()
 if kind=='ACQUIRE':
  assert not active,('overlapping io-sprg wrapper',active,line)
  k=int(re.match(r'k=(\d+) ',rest)[1]);assert k in [1,3]
  if k==3:assert 'lake exe cache get ' in rest;count3+=1
  active[pid]=dict(stamp=stamp,k=k);max_wrappers=max(max_wrappers,len(active));events.append(dict(pid=pid,start=stamp,k=k,command=rest.split(' cmd=',1)[1]))
 elif kind=='RELEASE':
  assert pid in active,('unmatched release',line)
  before=active.pop(pid)
  event=next(x for x in reversed(events) if x['pid']==pid and 'end' not in x);event['end']=stamp
  event['seconds']=int((datetime.datetime.fromisoformat(stamp.replace('Z','+00:00'))-datetime.datetime.fromisoformat(before['stamp'].replace('Z','+00:00'))).total_seconds())
 elif kind=='REAP':
  dead=re.search(r'dead=(\d+)',rest)
  if dead and dead[1] in active:
   active.pop(dead[1])
   event=next(x for x in reversed(events) if x['pid']==dead[1] and 'end' not in x)
   event['reaped_at']=stamp;event['termination']='No RELEASE recorded; wrapper PID observed dead and reaped before next acquisition. End time/cause and child-process history are not inferred.'
 elif kind!='REAP':raise RuntimeError(line)
if a.require_closed:assert not active,active
(out/'slots-io-sprg.log').write_text('\n'.join(lines)+'\n')
(out/'slot-summary.json').write_text(json.dumps(dict(as_of=datetime.datetime.now(datetime.timezone.utc).isoformat(),lines=len(lines),acquisitions=len(events),max_concurrent_job_wrappers=max_wrappers,cache_k3_acquisitions=count3,active=active,all_logged_acquisitions_serial_after_recorded_reaps=True,unreleased_reaped=[e for e in events if 'reaped_at' in e],source='/Users/seyoonr/.lean-slots/slots.log',qualification='Wrapper-event audit of tagged io-sprg commands; not an independent process-history audit of all host jobs.',events=events),indent=1)+'\n');print('SLOT_HISTORY_SERIAL',len(events),'active',len(active),'cache_k3',count3)
