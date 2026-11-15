"""Prepare full-largest-request-set sensitivity pilot for a selected batch size."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo', type=Path, default=Path('/private/tmp/hash-sign-fill/repo'))
parser.add_argument('--out', required=True, type=Path)
parser.add_argument('--chunk', type=int, default=1000)
args = parser.parse_args()
if args.chunk <= 0:
    parser.error('--chunk must be positive')
spec = importlib.util.spec_from_file_location('hash_sign_pilot_adapter', HERE / 'prepare.py')
adapter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(adapter)
builder = adapter.load_builder(args.chunk)
records = [json.loads(p.read_text()) for p in (args.out / 'seal-B').glob('SealB_*.json')]
if not records:
    raise RuntimeError('prepare final B source/requests first')
record = max(records, key=lambda r: (len(r['rows']), r['label']))
target = 'TCSlib.Cryptography.padFin'
if target not in {r['spelling'] for r in record['rows']}:
    raise RuntimeError('largest request set lacks selected pilot target')
_, negative, positive = adapter.CONTROL_BODIES[target]
source_raw = subprocess.check_output(['git', '--no-optional-locks', '-C', str(args.repo), 'show',
             record['rev'] + ':' + record['source']])
imports = list(dict.fromkeys(['Lean', *builder.header(source_raw)['imports']]))
plan = []
for sealed in [False, True]:
    label = 'Pilot' + ('S' if sealed else 'U') + str(args.chunk)
    source = (''.join('import ' + m + '\n' for m in imports) +
              '\nset_option maxHeartbeats 0\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n\n').encode()
    if sealed:
        source += builder.seal_command(label, record['rows'], end=False)
    source += b'namespace HashSignBatchingPilot\n\n'
    negative_line = source.count(b'\n') + 1
    source += negative.encode() + b'\n' + positive.encode() + b'\nend HashSignBatchingPilot\n\n'
    if sealed:
        source += builder.seal_command(label, record['rows'], end=True)
    probe = adapter.capture_probe(args.repo, '.lake/hash-sign-rule10/' + args.out.name + '/' + label, args.out, source)
    plan.append(dict(probe, sealed=sealed, target=target, request_record=record['label'],
         requested=len(record['rows']) if sealed else 0, chunk=args.chunk, expected_errors=1 if sealed else 0,
         negative_line=negative_line, expected_failing_declaration='HashSignBatchingPilot.negative' if sealed else None))
adapter.dump(args.out / ('pilot-plan-' + str(args.chunk) + '.json'), plan)
for path in [Path(__file__), HERE / 'prepare.py', HERE / 'run_probe.py']:
    raw = path.read_bytes()
    adapter.write(args.out / 'tool-versions' / (path.stem + '-' + hashlib.sha256(raw).hexdigest() + '.py'), raw)
print(json.dumps({'request_record': record['label'], 'full_requests': len(record['rows']), 'chunk': args.chunk, 'probes': plan}))
