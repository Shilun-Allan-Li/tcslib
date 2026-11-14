"""Run a variant's complete prepared seal set serially, stopping at any failure."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--out', required=True, type=Path)
p.add_argument('--variant', required=True, choices=['A', 'B'])
p.add_argument('--prefix', required=True)
p.add_argument('--skip-owner', action='append', default=[], help='Owner basename already passed in retained earlier batch')
p.add_argument('--first-owner', help='Prioritize one owner basename')
args = p.parse_args()
records = [(path, json.loads(path.read_text())) for path in (args.out / ('seal-' + args.variant)).glob('Seal' + args.variant + '_*.json')]
if not records:
    raise RuntimeError('no prepared seal records')
priority = ['HashAndSign', 'ForwardHandler', 'ForwardGame', 'CollisionGame', 'FixedGame',
            'CollisionHandler', 'CodecReaders', 'OneQuery', 'OneQuerySampling', 'Authentication']
if args.first_owner:
    priority.remove(args.first_owner)
    priority.insert(0, args.first_owner)
records.sort(key=lambda pair: priority.index(pair[1]['module'].rsplit('.', 1)[-1]))
plan = [{'ordinal': i, 'record': str(path), 'module': row['module'], 'probe_module': row['probe_module'],
         'requested': row['requested'], 'source_sha256': row['source_sha256'],
         'execution': 'retained earlier pass' if row['module'].rsplit('.', 1)[-1] in args.skip_owner else 'planned'}
         for i, (path, row) in enumerate(records, 1)]
(args.out / ('run-' + args.variant + '-plan.json')).write_text(json.dumps(plan, indent=2) + '\n')
raw = Path(__file__).read_bytes()
(args.out / 'tool-versions' / ('run_seals-' + hashlib.sha256(raw).hexdigest() + '.py')).write_bytes(raw)
for i, (path, row) in enumerate(records, 1):
    if row['module'].rsplit('.', 1)[-1] in args.skip_owner:
        print('SKIP retained earlier pass:', row['module'], flush=True)
        continue
    label = args.prefix + '-' + str(i).zfill(2)
    status = {'stage': 'running', 'ordinal': i, 'total': len(records), 'owner': row['module'], 'label': label}
    (args.out / ('run-' + args.variant + '-status.json')).write_text(json.dumps(status, indent=2) + '\n')
    subprocess.run([sys.executable, '-I', str(HERE / 'run_probe.py'), row['probe_module'], label,
                    '--out', str(args.out), '--record', str(path)], check=True)
    result = json.loads((args.out / (label + '.json')).read_text())
    log = HERE.parents[1] / 'logs' / (label + '.log')
    guards = subprocess.run([sys.executable, '-I', str(HERE / 'verify_guards.py'), '--record', str(path),
           '--log', str(log), '--out', str(args.out / (label + '.guards.json'))])
    if result['rc'] != 0 or result['error_count'] != 0 or guards.returncode != 0:
        status.update(stage='failed', result=result, guard_verifier_exit=guards.returncode)
        (args.out / ('run-' + args.variant + '-status.json')).write_text(json.dumps(status, indent=2) + '\n')
        raise SystemExit('SEAL FAILURE: ' + json.dumps(result))
status = {'stage': 'complete', 'variant': args.variant, 'modules': len(records), 'all_proofs_passed': True,
          'all_native_guard_coverage_verified': True, 'retained_earlier_owners': args.skip_owner}
(args.out / ('run-' + args.variant + '-status.json')).write_text(json.dumps(status, indent=2) + '\n')
print(json.dumps(status))
