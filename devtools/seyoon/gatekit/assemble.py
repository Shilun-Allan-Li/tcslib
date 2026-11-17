"""Build a gate's records payload under $GATE/records-payload: the evidence files, the gzip+base64
data carrier holding every log and input, and its recovery map. Copy the payload into the gate's
records folder afterwards. gate.json may add `evidence_files` ({published name: path in $GATE})."""
import base64, gzip, hashlib, json, os, subprocess
from pathlib import Path

G = Path(os.environ['GATE']); KIT = Path(__file__).resolve().parent
CFG = json.loads((G/'gate.json').read_text()); R = CFG['repo']
head = json.loads((G/'driver-request.json').read_text())['head']
base = subprocess.check_output(['git', '-C', R, 'rev-parse', CFG['base']]).decode().strip()
out = G/'records-payload'; assert not out.exists()
gate = Path(CFG['records_gate']); ev = gate/CFG.get('evidence_subdir', 'evidence')
sha = lambda b: hashlib.sha256(b).hexdigest()
dump = lambda x: (json.dumps(x, ensure_ascii=False, indent=1) + '\n').encode()
git = lambda *a: subprocess.check_output(['git', '-C', R, *a])
load = lambda p: json.loads((G/p).read_text())

rep = load('replay/RESULT.json'); assert rep['pass'] and rep['head'] == head and rep['failed'] == 0
src = load('SOURCE.json'); assert src['head'] == head
owners = [r['path'] for r in src['owner_source']]
assert git('diff', '--name-only', base + '...' + head, '--', '*.lean').decode().split() == sorted(owners)
# Gate 154: stage 2 is based on stage 1's head, which #349 merged; the merge-base's Lean equals the base's.
mb = git('merge-base', base, head).decode().strip()
assert mb == base or not git('diff', '--name-only', mb, base, '--', '*.lean').decode().split()
seal = load('seals/RESULT.json')
meta = load('metadata/RESULT.json') if (G/'metadata/RESULT.json').exists() else {}
disp = load('screen/PAIR-DISPOSITIONS.json')
assert open(G/'screen/HEAD/screen.txt').readline().strip() == disp['head_summary']

files = {}
def add(n, raw): assert n not in files, n; files[n] = raw
def tree(label, p, skip=()):
    for f in sorted(p.rglob('*')):
        if f.is_file() and not any(s in f.parts for s in skip):
            add(f'{label}/{f.relative_to(p).as_posix()}', f.read_bytes())
tree('replay', G/'replay', skip=('runtime',))
for d in ('seals',):
    tree(d, G/d, skip=('.lake',))
for d in sorted(G.glob('controls-part*')): tree(d.name, d, skip=('.lake',))
tree('metadata', G/'metadata', skip=('.lake', 'runtime'))
tree('qa', G/'qa', skip=('.lake',))
for f in ('checks.out', 'qa.log', 'seals.out', 'replay.out'):
    add('logs/' + f, (G/f).read_bytes())
for side, rev in (('HEAD', head), ('BASE', base)):
    for f in ('screen.txt', 'screen.err'): add(f'screen/{side}/{f}', (G/'screen'/side/f).read_bytes())
    for p in (G/('POPULATION.txt' if side == 'HEAD' else 'POPULATION-BASE.txt')).read_text().split():
        raw = git('show', f'{rev}:{p}'); assert raw == (G/'screen'/side/'export'/p).read_bytes()
        add(f'population/{side}/{p}.txt', raw)
add('screen/pairdiff.txt', (G/'screen/pairdiff.txt').read_bytes())
# The Lean-backed explicit-argument sweep (gate 144's G144-01 method).
for f in ('SUMMARY.json', 'run.out', 'CITATION-HOMES.json'):
    add('defsweep/' + f, (G/'defsweep'/f).read_bytes())  # the sweep scripts themselves are carried under kit/
add('defsweep/Kinds.lean', (G/'dsw/TCSlib/Scratch/Kinds.lean').read_bytes())
for f in sorted((G/'dsw/TCSlib/Scratch/DefSweep').glob('*')):
    add('defsweep/checks/' + f.name, f.read_bytes())
for f in sorted((G/'defsweep').glob('*.log')):
    add('defsweep/logs/' + f.name, f.read_bytes())
add('scripts/copy-text-screen-v3.py', git('show', f'{head}:scripts/copy-text-screen-v3.py'))
for p in owners:
    add('source/campaign/' + p + '.txt', git('show', base + ':' + p))
add('patch/campaign-to-head.patch', git('diff', base + '...' + head, '--', '*.lean'))
add('checks/irreducible.json', (KIT/'templates/irreducible.json').read_bytes())
# Earlier runs on superseded heads, moved aside as runN/ folders, are carried too.
for d in sorted(G.glob('run[0-9]*')):
    if d.is_dir(): tree(d.name, d, skip=('runtime', '.lake', 'dsw', 'dsw-ov', 'export', 'compiled-source'))
add('screen/PAIR-DISPOSITIONS.json', (G/'screen/PAIR-DISPOSITIONS.json').read_bytes())
for f in sorted(KIT.rglob('*')):
    if f.is_file() and '__pycache__' not in f.parts:
        add('kit/' + f.relative_to(KIT).as_posix(), f.read_bytes())
for p in ('gate.json', 'driver-request.json', 'CHANGED.txt', 'POPULATION.txt', 'POPULATION-BASE.txt', 'pair-notes.json'):
    if (G/p).exists(): add('gate/' + p, (G/p).read_bytes())
inv = []; blobs = {}
for n, raw in sorted(files.items()):
    h = sha(raw); inv.append({'path': n, 'sha256': h, 'bytes': len(raw)})
    if h not in blobs:
        z = gzip.compress(raw, mtime=0)
        blobs[h] = {'encoding': 'gzip+base64', 'gzip_sha256': sha(z), 'gzip_bytes': len(z),
                    'gzip_base64': base64.b64encode(z).decode()}
for r in inv: assert gzip.decompress(base64.b64decode(blobs[r['sha256']]['gzip_base64'])) == files[r['path']]
carrier = dump({'files': inv, 'blobs': blobs}); assert len(carrier) < 55_000_000
T = {ev/'SOURCE.json': dump(src), ev/'REPLAY.json': dump(rep), ev/'PAIR-DISPOSITIONS.json': dump(disp),
     ev/'DATA-CARRIER.json': carrier,
     ev/'DEFSWEEP-SUMMARY.json': (G/'defsweep/SUMMARY.json').read_bytes(), ev/'CITATION-HOMES.json': (G/'defsweep/CITATION-HOMES.json').read_bytes(),
     ev/'DATA-RECOVERY-MAP.json': dump({'files': inv, 'logical_files': len(inv), 'carrier_sha256': sha(carrier),
                                        'carrier_bytes': len(carrier), 'all_recovered_bytes_verified': True})}
for name, rel in CFG.get('evidence_files', {}).items():
    T[ev/name] = (G/rel).read_bytes()
for p, raw in T.items():
    d = out/p; d.parent.mkdir(parents=True, exist_ok=True); d.write_bytes(raw)
print('head', head, 'logical files', len(inv), 'carrier bytes', len(carrier))
