"""Retire only verified stopped old Python coordinator; never signal native children."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

pid = int(sys.argv[1])
evidence = Path('/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence')
output = evidence / 'logs/final18-native-r1/coordinator-retirement.json'
assert not output.exists()
def processes():
    result=[]
    raw=subprocess.check_output(['ps','-axo','pid,ppid,state,command'],text=True)
    for line in raw.splitlines()[1:]:
        p,pp,s,c=line.strip().split(None,3)
        result.append(dict(pid=int(p),ppid=int(pp),state=s,command=c))
    return result
before=processes()
own=next(x for x in before if x['pid']==pid)
assert own['state'].startswith('T')
assert 'run_final18_native.py' in own['command'] and '--attempt final18-native-r1' in own['command']
desc={pid}
while True:
    updated=desc|{x['pid'] for x in before if x['ppid'] in desc}
    if updated==desc:break
    desc=updated
tree=[x for x in before if x['pid'] in desc]
assert all(x['pid']==pid or x['state'].startswith('Z') for x in tree),tree
summary=json.loads((evidence/'logs/seals/finalr2averaging-native-r1/summary.json').read_text())
assert summary['queue_complete'] and summary['status_counts']=={'SOURCE_PASS':2,'CONTROL_PASS':6}
record=dict(timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    reason='Qualified cached runner adopts all successful native checks; retire old stopped Python coordinator without resuming it',
    signaled_pid=pid,signal='SIGKILL',before=tree,no_live_native_descendants=True,
    native_phases_complete=4,canonical_native_logs_preserved=True,
    old_coordinator_log_partial_because_intentional_phase_boundary_pause=True,
    old_phase4_scan_and_summary_completed_by_new_adopting_runner=True,
    replacement_queue=str(evidence/'preparation/final18-r2/cached-collectors-r3/queue.json'),
    tool_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
output.with_suffix('.tool.py').write_bytes(Path(__file__).read_bytes())
# No live native process is signaled: only the stopped Python coordinator above.
os.kill(pid,signal.SIGKILL)
time.sleep(0.2)
after=processes()
remaining=[x for x in after if x['pid']==pid]
assert not remaining or all(x['state'].startswith('Z') for x in remaining)
record['after']=remaining
output.write_text(json.dumps(record,indent=2)+'\n')
print(output)
