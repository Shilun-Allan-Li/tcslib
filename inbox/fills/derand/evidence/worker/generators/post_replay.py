"""Wait without a Lean slot, then finish the verification-tree evidence serially."""
import datetime
import json
from pathlib import Path
import subprocess
import time

log = Path('evidence/logs/post-replay.log')
def record(message):
    text = datetime.datetime.now(datetime.timezone.utc).isoformat() + ' ' + message
    with log.open('a') as dest:
        print(text, file=dest)
    print(text, flush=True)

record('Waiting for the existing final-full writer; no slot held by this controller')
while True:
    content = Path('evidence/logs/final-full/results.jsonl').read_text()
    lines = content.splitlines() if content.endswith('\n') else content.splitlines()[:-1]
    rows = [json.loads(line) for line in lines]
    if any(row['exit'] or row['errors'] for row in rows):
        raise RuntimeError('Final replay failed; no post-check Lean run started')
    if len(rows) == 387:
        break
    time.sleep(5)
record('387/387 final modules passed; starting post-checks in the now-idle olean tree')
commands = [
 ['python3', '-I', 'evidence/tools/check_modules.py', 'final-replay-axioms', 'evidence/axioms/final/order.txt'],
 ['python3', '-I', 'evidence/tools/check_modules.py', 'final-replay-paths', 'evidence/axioms/final/host-paths-order.txt'],
 ['python3', '-I', 'evidence/tools/final_validate.py'],
 ['python3', '-I', 'evidence/tools/check_sorries.py', '.', 'final-full',
  '--removed', 'exists_seedMajorityTM', '--removed', 'seedMajority_mem_DTIME',
  '--removed', 'bpp_subset_dtime_subexp'],
 ['python3', '-I', 'evidence/tools/frozen_headers.py', '--out', 'evidence/headers/final-replay'],
 ['python3', '-I', 'evidence/tools/lint_compare.py'],
 ['python3', '-I', 'evidence/tools/name_clash_all.py'],
 ['python3', '-I', 'evidence/tools/explicit_unfold_scan.py'],
]
for index, command in enumerate(commands, 1):
    destination = Path('evidence/logs') / f'post-replay-{index:02}.log'
    with destination.open('w') as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    record(f'{command}: exit={result.returncode} log={destination}')
    if result.returncode:
        print(destination.read_text()[-14000:], flush=True)
        raise SystemExit(result.returncode)
record('POST-REPLAY PASS')
