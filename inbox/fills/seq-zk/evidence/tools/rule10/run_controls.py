"""Run active paired controls serially through run_probe/check_module; no timeout."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out', required=True, type=Path)
parser.add_argument('--repo', default='/private/tmp/hash-sign-fill/repo')
parser.add_argument('--prefix', required=True)
parser.add_argument('--skip', action='append', default=[], help='VARIANT:TARGET already checked by a retained pair')
args = parser.parse_args()
plan = json.loads((args.out / 'controls-plan.json').read_text())
for index, row in enumerate((r for r in plan if 'module' in r), 1):
    if row['variant'] + ':' + row['target'] in args.skip:
        print('SKIP retained completed pair:', row['variant'], row['target'], flush=True)
        continue
    label = args.prefix + '-' + str(index).zfill(2)
    cmd = [sys.executable, '-I', str(Path(__file__).with_name('run_probe.py')),
           row['module'], label, '--out', str(args.out), '--repo', args.repo,
           '--expected-errors', str(row['expected_error_count'])]
    if row['expected_error_count'] == 1:
        cmd += ['--negative-line', str(row['negative_start_line'])]
    result = subprocess.run(cmd)
    if result.returncode != 0:
        raise SystemExit('Control expectation failed; stopped at ' + row['module'])
print('ALL PAIRED CONTROL EXPECTATIONS PASSED')
