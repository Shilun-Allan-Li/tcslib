"""Compare every direct Lamport-helper Mathlib import with the issued roots.

This preserves the source of the earlier inline roots audit. Run as python3 -I
from the proof checkout; output stays at its final evidence path.
"""
from pathlib import Path

base = Path('/private/tmp/tcslib-lamport-01a1d88f')
roots = next((base / 'issued').rglob('roots.txt'))
issued = set(roots.read_text().splitlines())
items = []
for source in sorted(Path('TCSlib/Cryptography/Authentication/Signatures/Lamport').glob('*.lean')):
    for line in source.read_text().splitlines():
        if line.startswith('import Mathlib'):
            module = line.split()[1]
            items.append((str(source), module, module in issued))
log = base / 'delivery/lamport/evidence/logs/helper-mathlib-roots-audit.log'
with log.open('w') as stream:
    stream.write(f'Issued roots source: {roots}\nIssued roots count: {len(issued)}\n')
    for source, module, present in items:
        stream.write(f'{source}: {module} ISSUED={present}\n')
    missing = sorted({module for _, module, present in items if not present})
    stream.write(f'Unlisted direct helper Mathlib roots: {missing}\n')
print(log.read_text())
