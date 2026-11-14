"""Run one prepared probe through the required retained check_module.py driver.

No timeout is imposed. Raw logs remain in evidence/logs from their creation;
this wrapper appends a concise machine-readable record to phase results.jsonl.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('module')
parser.add_argument('label')
parser.add_argument('--out', required=True, type=Path)
parser.add_argument('--repo', default='/private/tmp/hash-sign-fill/repo', type=Path)
parser.add_argument('--record', type=Path)
parser.add_argument('--expected-errors', type=int)
parser.add_argument('--negative-line', type=int)
args = parser.parse_args()
out = args.out.resolve()
out.mkdir(parents=True, exist_ok=True)
if (out / 'STOP_BEFORE_NEXT_PROBE').exists():
    raise SystemExit('Deferred before starting next probe by coordinator request.')
rawlog = root / 'logs' / (args.label + '.log')
if rawlog.exists():
    raise SystemExit('refusing existing probe label')
start = datetime.datetime.now(datetime.timezone.utc).isoformat()
tick = time.monotonic()
driver_log = out / (args.label + '.driver.log')
with driver_log.open('w') as f:
    proc = subprocess.run([sys.executable, '-I', str(root / 'tools/check_module.py'), args.module, args.label],
          cwd=args.repo, stdout=subprocess.DEVNULL, stderr=f)
text = rawlog.read_text() if rawlog.exists() else ''
errors = []
for match in re.finditer(r'([^\n]+\.lean):(\d+):(\d+): error(?:\([^\n)]*\))?:([^\n]*)', text):
    errors.append({'probe_path': match[1], 'probe_line': int(match[2]), 'column': int(match[3]), 'message': match[4].strip()})
record = None
if args.record:
    record = json.loads(args.record.read_text())
    lmap = {r['probe_line']: r['source_line'] for r in record['source_to_probe_lines']}
    original = subprocess.check_output(['git', '--no-optional-locks', '-C', str(args.repo), 'show',
                record['rev'] + ':' + record['source']], text=True).splitlines()
    ns, declarations = [], []
    for i, line in enumerate(original, 1):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            ns.append(m[1])
        m = re.match(r'^(?:(?:private|noncomputable|protected|nonrec)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s(:{\[]+)', line)
        if m:
            declarations.append((i, '.'.join(ns + [m[1]])))
        if re.match(r'^end\b', line) and ns:
            ns.pop()
    for err in errors:
        line = lmap.get(err['probe_line'])
        err['source_line'] = line
        err['declaration'] = next((name for i, name in reversed(declarations) if line is not None and i <= line), 'HARNESS')
rss = re.search(r'(\d+)\s+maximum resident set size', text)
source = args.repo / (args.module + '.lean')
result = {'module': args.module, 'label': args.label, 'rc': proc.returncode,
          'start': start, 'end': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'elapsed_seconds': round(time.monotonic() - tick, 3),
          'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'raw_log': str(rawlog), 'raw_log_sha256': hashlib.sha256(rawlog.read_bytes()).hexdigest() if rawlog.exists() else None,
          'error_count': len(errors), 'errors': errors,
          'maxrss_bytes_macos': int(rss[1]) if rss else None,
          'expected_error_count': args.expected_errors,
          'failing_declarations': sorted(set(e.get('declaration', 'CONTROL_OR_PROBE') for e in errors))}
if args.expected_errors is not None:
    result['expectation_passed'] = len(errors) == args.expected_errors and ((proc.returncode == 0) == (args.expected_errors == 0))
    if args.negative_line is not None and args.expected_errors == 1:
        result['expectation_passed'] = result['expectation_passed'] and len(errors) == 1 and errors[0]['probe_line'] == args.negative_line
with (out / 'results.jsonl').open('a') as f:
    print(json.dumps(result), file=f)
(out / (args.label + '.json')).write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ['errors']}))
if args.expected_errors is not None:
    raise SystemExit(0 if result['expectation_passed'] else 1)
