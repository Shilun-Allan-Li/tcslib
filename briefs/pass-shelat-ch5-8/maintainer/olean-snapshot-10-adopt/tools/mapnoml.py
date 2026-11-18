"""mapnoml.py <dir> <map.tsv> [<ref-map.tsv>] (Gate 44, maintainer): snapmap.py's map format over <dir> with the Mathlib/
overlay excluded (the map that `snapmap.py make` produces once recipe step 6 removes Mathlib/). With a reference map, also
prints the comparison (equal / changed / added / removed)."""
import sys, os, hashlib
d, out = sys.argv[1:3]; files = {}
for r, ds, fs in os.walk(d):
    rel = os.path.relpath(r, d)
    if rel == 'Mathlib' or rel.startswith('Mathlib/'): continue
    for f in fs:
        p = os.path.join(r, f); q = os.path.relpath(p, d)
        assert not os.path.islink(p) and f.endswith('.olean'), q
        files[q[:-6]] = hashlib.sha256(open(p, 'rb').read()).hexdigest()
with open(out, 'w') as o:
    for m in sorted(files): o.write(f'{m}\t{files[m]}\n')
print(f'{out}: entries {len(files)}; sha256 {hashlib.sha256(open(out, "rb").read()).hexdigest()}')
if len(sys.argv) > 3:
    M = dict(l.rstrip('\n').split('\t') for l in open(sys.argv[3]))
    eq = sum(1 for m in files if M.get(m) == files[m]); ch = sorted(m for m in files if m in M and M[m] != files[m])
    print(f'vs {sys.argv[3]}: equal {eq}; changed {len(ch)} {ch}; added {sorted(set(files) - set(M))}; removed {sorted(set(M) - set(files))}')
