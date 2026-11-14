"""Match every delivered Lean source to its successful canonical module checks.

Run with python3 -I. Reports all matching attempts, never a silent latest-attempt
choice. Earlier source/attempt records are preserved. No compiler is invoked.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', required=True)
parser.add_argument('--evidence', required=True)
parser.add_argument('--commit', required=True)
parser.add_argument('--output', required=True)
args = parser.parse_args()
root, evidence = Path(args.root), Path(args.evidence)
base = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
paths = subprocess.check_output(['git', '-C', str(root), 'diff', '--name-only', base,
                                args.commit, '--', '*.lean'], text=True).splitlines()
results = [json.loads(line) for line in
           (evidence / 'logs/helper-checks/results.jsonl').read_text().splitlines()]
records = []
for path in paths:
    raw = subprocess.check_output(['git', '-C', str(root), 'show', args.commit + ':' + path])
    value = hashlib.sha256(raw).hexdigest()
    matches = [row for row in results if row['module'] == path[:-5]
               and row['exit'] == 0 and row['source_sha256'] == value]
    assert matches, 'no source-matching successful canonical check: ' + path
    checks = []
    for row in matches:
        log = evidence / row['log']
        snapshot = log.with_suffix('.source.lean')
        assert snapshot.read_bytes() == raw, snapshot
        text = log.read_text()
        assert 'source-sha256=' + value in text and text.rstrip().endswith('exit=0'), log
        checks.append(dict(attempt=row['attempt'], log=row['log'],
                           log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
                           source_snapshot=str(snapshot.relative_to(evidence))))
    records.append(dict(path=path, source_sha256=value, successful_exact_source_checks=checks))
output = evidence / args.output
assert not output.exists(), output
output.write_text(json.dumps(dict(commit=args.commit, all_sources_have_exact_success=True,
                                  compiler_run=False, records=records), indent=2) + '\n')
print(json.dumps(dict(commit=args.commit, files=len(records),
                     all_sources_have_exact_success=True), indent=2))
