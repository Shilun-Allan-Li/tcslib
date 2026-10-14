"""Stage byte-identical, flattened copies of a screen population for copy-text-screen.py.

The screen labels files by basename and treats two declarations with the same basename and
name as one, so a pair between two same-named files (for example `Build/Catalog.lean` and
`Build/Contract/Catalog.lean`) would be dropped and the labels would be ambiguous. This tool
copies every population file to `<flat-dir>/<encoded>.lean`, where `<encoded>` is the path
below `TCSlib/Complexity/` with `/` replaced by `.` (for example
`TuringMachine.Build.Catalog.lean`), checks each copy byte for byte (SHA-256), and writes the
encoded names, in population order, to `<flat-dir>/NAMES.txt`.

Usage:
  python3 -I flatscreen.py <repo-root> <population.txt> <flat-dir> [<repo-path>=<file> ...]
A `<repo-path>=<file>` argument stages <file> under <repo-path>'s encoded name instead of the
repository's file (to screen a candidate CodeSimulator.lean before committing it).
Then run, from any directory:
  python3 -I <repo-root>/audits/evidence/retrofit/copy-text-screen.py <flat-dir> \
    $(cat <flat-dir>/NAMES.txt)
"""
import hashlib, os, sys

root, pop, flat = sys.argv[1], sys.argv[2], sys.argv[3]
subst = dict(a.split('=', 1) for a in sys.argv[4:])
PREFIX = 'TCSlib/Complexity/'
paths = [l.strip() for l in open(pop, encoding='utf-8') if l.strip() and not l.startswith('#')]
assert len(paths) == len(set(paths)), 'duplicate population entries'
assert all(p.startswith(PREFIX) and p.endswith('.lean') for p in paths), 'unexpected path'
assert set(subst) <= set(paths), ('substitution outside the population', set(subst) - set(paths))
os.makedirs(flat, exist_ok=True)
assert not [f for f in os.listdir(flat) if f.endswith('.lean')], 'flat dir must start empty'
names = []
for p in paths:
    enc = p[len(PREFIX):].replace('/', '.')
    src = subst.get(p, os.path.join(root, p))
    data = open(src, 'rb').read()
    dst = os.path.join(flat, enc)
    assert not os.path.exists(dst), ('encoded-name collision', enc)
    open(dst, 'wb').write(data)
    assert hashlib.sha256(open(dst, 'rb').read()).digest() == hashlib.sha256(data).digest()
    names.append(enc)
    print(f'{hashlib.sha256(data).hexdigest()}  {enc}  <-  {src}')
open(os.path.join(flat, 'NAMES.txt'), 'w', encoding='utf-8').write('\n'.join(names) + '\n')
print(f'OK: {len(names)} files staged byte for byte ({len(subst)} substituted)')
