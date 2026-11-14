"""Run one Lean module at a time, recording raw logs directly at final paths."""
import datetime
import json
from pathlib import Path
import subprocess
import sys

root, evidence, order, phase = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]), sys.argv[4]
logs = evidence / 'logs' / phase
logs.mkdir(parents=True, exist_ok=True)
for index, module in enumerate(order.read_text().splitlines(), 1):
    if not module.strip():
        continue
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    log = logs / (module.replace('/', '_') + '.log')
    command = ['python3', '-I', str(evidence / 'tools/lean_host_guard.py'), '--',
               '/usr/bin/time', '-l', 'bash', 'scripts/lean_check_tree.sh', module]
    print(f'{index}: START {module}', flush=True)
    with log.open('w') as output:
        output.write(f'START {start}\nCOMMAND {command!r}\n')
        output.flush()
        result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
        end = datetime.datetime.now(datetime.timezone.utc).isoformat()
        output.write(f'END {end}\nEXIT {result.returncode}\n')
    with (logs / 'results.jsonl').open('a') as results:
        results.write(json.dumps(dict(module=module, start=start, end=end,
                                     exit=result.returncode, log=str(log.relative_to(evidence)))) + '\n')
    print(f'{index}: END {module}: {result.returncode}', flush=True)
    if result.returncode:
        print(log.read_text()[-6000:], flush=True)
        sys.exit(result.returncode)
