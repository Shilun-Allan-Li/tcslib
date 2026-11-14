"""Run one positive/negative batching pilot serially through the shared checker."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--out', required=True, type=Path)
p.add_argument('--chunk', type=int, default=1000)
p.add_argument('--prefix', default='rule10-final-pilot')
args = p.parse_args()
plan = json.loads((args.out / ('pilot-plan-' + str(args.chunk) + '.json')).read_text())
for row in plan:
    label = args.prefix + ('-S-' if row['sealed'] else '-U-') + str(args.chunk)
    cmd = [sys.executable, '-I', str(HERE / 'run_probe.py'), row['module'], label,
           '--out', str(args.out), '--expected-errors', str(row['expected_errors'])]
    if row['sealed']:
        cmd += ['--negative-line', str(row['negative_line'])]
    result = subprocess.run(cmd)
    if result.returncode:
        raise SystemExit('Pilot failed; retain evidence and revert batching to500.')
    if row['sealed']:
        record = args.out / 'seal-B' / (row['request_record'] + '.json')
        log = HERE.parents[1] / 'logs' / (label + '.log')
        subprocess.run([sys.executable, '-I', str(HERE / 'verify_guards.py'), '--record', str(record),
                       '--log', str(log), '--out', str(args.out / (label + '.guards.json'))], check=True)
print('BATCHING PILOT PASSED; full request identity/install/mask/EOF coverage independently verified.')
