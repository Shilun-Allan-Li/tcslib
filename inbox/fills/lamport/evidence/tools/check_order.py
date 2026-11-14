"""Run one Lean module at a time, recording raw logs directly at final paths."""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

root, evidence, order, phase = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]), sys.argv[4]
logs = evidence / 'logs' / phase
logs.mkdir(parents=True, exist_ok=False)
for index, module in enumerate(order.read_text().splitlines(), 1):
    if not module.strip():
        continue
    attempt = 0
    attempt_records = []
    while True:
        attempt += 1
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        source_path = root / (module + '.lean')
        source_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
        suffix = '' if attempt == 1 else f'.host{attempt}'
        log = logs / (module.replace('/', '_') + suffix + '.log')
        command = ['python3', '-I', str(evidence / 'tools/lean_host_guard.py'), '--',
                   '/usr/bin/time', '-l', 'bash', 'scripts/lean_check_tree.sh', module]
        print(f'{index}: START {module} attempt {attempt}', flush=True)
        with log.open('x') as output:
            output.write(f'START {start}\nCOMMAND {command!r}\n')
            output.flush()
            result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
            source_after_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
            end = datetime.datetime.now(datetime.timezone.utc).isoformat()
            output.write(f'END {end}\nEXIT {result.returncode}\n')
            output.write(f'SOURCE_SHA256 {source_hash}\nSOURCE_AFTER_SHA256 {source_after_hash}\n')
        record = dict(module=module, attempt=attempt, start=start, end=end,
                      exit=result.returncode, log=str(log.relative_to(evidence)),
                      source_sha256=source_hash, source_after_sha256=source_after_hash)
        with (logs / 'attempts.jsonl').open('a') as attempts:
            attempts.write(json.dumps(record) + '\n')
        attempt_records.append(record)
        if source_hash != source_after_hash:
            raise RuntimeError('module source changed during check: ' + module)
        cap_interruption = (result.returncode == 130 and
            'INTERRUPTED: stopping only our Lean child' in log.read_text())
        if not cap_interruption:
            break
        print(f'{index}: RETRY shared-cap interruption {module} attempt {attempt}', flush=True)
    # One terminal result per module; all attempts, including every host interruption,
    # are separately preserved rather than silently selecting a duplicate last result.
    with (logs / 'results.jsonl').open('a') as results:
        results.write(json.dumps(dict(module=module, start=start, end=end,
                                     exit=result.returncode, log=str(log.relative_to(evidence)),
                                     source_sha256=source_hash,
                                     source_after_sha256=source_after_hash,
                                     attempts=attempt_records)) + '\n')
    print(f'{index}: END {module}: {result.returncode}', flush=True)
    if result.returncode:
        print(log.read_text()[-6000:], flush=True)
        sys.exit(result.returncode)
    if source_hash != source_after_hash:
        raise RuntimeError('module source changed during check: ' + module)
