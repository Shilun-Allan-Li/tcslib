"""Reconcile actual final A/B source checks across preserved batching attempts."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--final', required=True, type=Path, help='Final collector/owner directory')
p.add_argument('--batch', action='append', required=True, type=Path)
p.add_argument('--allow-incomplete', action='store_true')
p.add_argument('--repo', type=Path, default=Path('/private/tmp/hash-sign-fill/repo'))
p.add_argument('--final-rev', default='HEAD')
args = p.parse_args()
owners = (args.final / 'owners.txt').read_text().splitlines()
final_rev = subprocess.check_output(['git', '--no-optional-locks', '-C', str(args.repo), 'rev-parse', args.final_rev], text=True).strip()
latest_hashes = {owner: hashlib.sha256(subprocess.check_output(['git', '--no-optional-locks', '-C', str(args.repo),
              'show', final_rev + ':' + owner.replace('.', '/') + '.lean'])).hexdigest() for owner in owners}
prepared = {}
for directory in args.batch:
    for path in directory.glob('seal-[AB]/Seal[AB]_*.json'):
        row = json.loads(path.read_text())
        prepared[row['probe_module']] = (path, row, path.parent.name[-1])
cells = {(owner, letter): [] for owner in owners for letter in 'AB'}
for directory in args.batch:
    results = directory / 'results.jsonl'
    if not results.exists():
        continue
    for line in results.read_text().splitlines():
        result = json.loads(line)
        if result['module'] not in prepared:
            continue
        path, record, letter = prepared[result['module']]
        if record['module'] not in owners:
            continue
        guards_path = directory / (result['label'] + '.guards.json')
        guards = json.loads(guards_path.read_text()) if guards_path.exists() else None
        log = Path(result['raw_log'])
        log_sha = hashlib.sha256(log.read_bytes()).hexdigest()
        valid = result['rc'] == 0 and result['error_count'] == 0 and guards is not None
        valid = valid and result['source_sha256'] == record['probe_sha256'] and log_sha == result['raw_log_sha256']
        valid = valid and guards['native_identity_install_mask_eof_complete'] and guards['request_count'] == record['requested']
        valid = valid and guards['raw_log_sha256'] == log_sha and guards['record_sha256'] == hashlib.sha256(path.read_bytes()).hexdigest()
        cells[(record['module'], letter)].append({'label': result['label'], 'source_commit': record['rev'],
             'source_sha256': record['source_sha256'], 'request_record': str(path), 'request_count': record['requested'],
             'raw_log': str(log), 'guard_audit': str(guards_path), 'batch_sizes': guards['batch_sizes'] if guards else None,
             'proof_and_full_guard_coverage_passed': valid,
             'matches_latest_source_bytes': record['source_sha256'] == latest_hashes[record['module']]})
matrix = [{'owner': owner, 'variant': letter, 'actual_checks': cells[(owner, letter)],
           'latest_source_sha256': latest_hashes[owner],
           'passed': any(r['proof_and_full_guard_coverage_passed'] and r['matches_latest_source_bytes'] for r in cells[(owner, letter)])}
          for owner in owners for letter in 'AB']
summary = {'owners': len(owners), 'expected_cells': len(matrix), 'passed_cells': sum(r['passed'] for r in matrix),
           'latest_source_commit': final_rev, 'complete': all(r['passed'] for r in matrix), 'matrix': matrix}
(args.final / 'seal-matrix.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'matrix'}))
if not summary['complete'] and not args.allow_incomplete:
    raise SystemExit('Final owner-by-variant matrix is incomplete or contains a failed guard/proof.')
