"""Retain every source-seal failure and link an exact-latest-byte passing repair."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--root', required=True, type=Path)
p.add_argument('--repo', default='/private/tmp/hash-sign-fill/repo', type=Path)
p.add_argument('--rev', default='HEAD')
args = p.parse_args()
records = {}
for path in args.root.rglob('seal-[AB]/Seal[AB]_*.json'):
    row = json.loads(path.read_text())
    records[row['probe_module']] = (row, path.parent.name[-1], path)
actual = []
for path in args.root.rglob('results.jsonl'):
    for line in path.read_text().splitlines():
        result = json.loads(line)
        if result.get('module') in records:
            row, variant, record_path = records[result['module']]
            actual.append((result, row, variant, path.parent))
latest = {}
for _, row, _, _ in actual:
    if row['module'] not in latest:
        raw = subprocess.check_output(['git', '--no-optional-locks', '-C', str(args.repo), 'show', args.rev + ':' + row['source']])
        latest[row['module']] = hashlib.sha256(raw).hexdigest()
passing = {}
for result, row, variant, directory in actual:
    guard_path = directory / (result['label'] + '.guards.json')
    guard = json.loads(guard_path.read_text()) if guard_path.exists() else {}
    if result['rc'] == 0 and result['error_count'] == 0 and guard.get('native_identity_install_mask_eof_complete') and row['source_sha256'] == latest[row['module']]:
        passing.setdefault((row['module'], variant), []).append({'label': result['label'], 'source_commit': row['rev'],
             'source_sha256': row['source_sha256'], 'raw_log': result['raw_log'], 'guard_audit': str(guard_path)})
failures = []
for result, row, variant, directory in actual:
    if result['rc'] != 0 or result['error_count']:
        for error in result['errors']:
            failures.append({'owner': row['module'], 'variant': variant, 'failed_source_commit': row['rev'],
                'failed_source_sha256': row['source_sha256'], 'raw_log': result['raw_log'], 'error': error,
                'latest_byte_passing_resolution': passing.get((row['module'], variant), [])})
summary = {'source_seal_diagnostics': len(failures), 'failures': failures,
           'all_have_latest_byte_passing_resolution': all(r['latest_byte_passing_resolution'] for r in failures)}
(args.root / 'source-seal-failure-ledger.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'failures'}))
