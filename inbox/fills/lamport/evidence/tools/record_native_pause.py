"""Record coordinated Python-driver pause, verifying native children finished."""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

driver = int(sys.argv[1])
evidence = Path('/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence')
root = Path('/private/tmp/tcslib-lamport-01a1d88f/proof')
output = evidence / 'logs/final18-native-r1/pause-after-averaging.json'
assert not output.exists()
raw = subprocess.check_output(['ps', '-axo', 'pid,ppid,state,command'], text=True)
processes = []
for line in raw.splitlines()[1:]:
    pid, ppid, state, command = line.strip().split(None, 3)
    processes.append(dict(pid=int(pid), ppid=int(ppid), state=state, command=command))
own = next(x for x in processes if x['pid'] == driver)
assert 'run_final18_native.py' in own['command'] and '--attempt final18-native-r1' in own['command']
assert own['state'].startswith('T')
descendants = {driver}
while True:
    new = descendants | {x['pid'] for x in processes if x['ppid'] in descendants}
    if new == descendants:
        break
    descendants = new
tree = [x for x in processes if x['pid'] in descendants]
assert all(x['pid'] == driver or x['state'].startswith('Z') for x in tree), tree
native_ours = [x for x in processes if str(root) in x['command'] and '/bin/lean ' in x['command']]
assert not native_ours, native_ours
phase = evidence / 'logs/seals/finalr2averaging-native-r1'
summary = json.loads((phase / 'summary.json').read_text())
assert summary['queue_complete'] and summary['status_counts'] == {'SOURCE_PASS': 2, 'CONTROL_PASS': 6}
records = [json.loads(x) for x in (phase / 'results.jsonl').read_text().splitlines()]
assert len(records) == 8
audit = json.loads((evidence / 'inputs/final-r2-order-audit.json').read_text())
hashes = {m: hashlib.sha256((root / (m + '.lean')).read_bytes()).hexdigest() for m in audit['source_sha256']}
assert hashes == audit['source_sha256']
result = dict(timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(), driver=own,
              descendants=tree, no_live_native_children=True, no_proof_native_processes=True,
              native_phases_complete=4, phase_summaries_and_scans_complete=3,
              current_phase='FinalR2Averaging', current_phase_native_summary=summary,
              phase_raw_log_directory=str(phase), source_hashes_unchanged=True,
              frozen_revision='47ced271090f45918645c842cd358c5079092754',
              pending_before_resume='Averaging seal selection, explicit unfold scan, source-after hash check, phase summary',
              tool_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
output.write_text(json.dumps(result, indent=2) + '\n')
output.with_suffix('.tool.py').write_bytes(Path(__file__).read_bytes())
print(output)
print(json.dumps({k: result[k] for k in ('native_phases_complete', 'phase_summaries_and_scans_complete', 'no_live_native_children')}))
