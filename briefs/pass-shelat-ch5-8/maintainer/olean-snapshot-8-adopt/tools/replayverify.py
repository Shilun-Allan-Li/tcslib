"""replayverify.py <dir> <ref-map.tsv> <ref-sha256>: rehash a replay tree (Mathlib/ overlay excluded) against its
recorded no-Mathlib map; report symlinks outside Mathlib/, other files, the Mathlib/ symlink count and Mathlib/ regular files."""
import sys, os, hashlib
d, ref, refsha = sys.argv[1:4]
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
rs = sha(ref); M = dict(l.rstrip('\n').split('\t') for l in open(ref))
files, links, other, mlinks, mfiles = {}, [], [], 0, []
for r, ds, fs in os.walk(d):
    for f in fs + [x for x in ds if os.path.islink(os.path.join(r, x))]:
        p = os.path.join(r, f); q = os.path.relpath(p, d); inml = q.startswith('Mathlib/')
        if os.path.islink(p):
            if inml: mlinks += 1
            else: links.append(q)
            continue
        if inml: mfiles.append((q, sha(p))); continue
        if q.endswith('.olean'): files[q[:-6]] = sha(p)
        else: other.append(q)
ex = sorted(set(files) - set(M)); mi = sorted(set(M) - set(files)); ch = sorted(m for m in files if m in M and M[m] != files[m])
ok = rs == refsha and not ex and not mi and not ch and not links and not other
print(f'{d}: ref {ref} sha256 {"OK" if rs == refsha else "MISMATCH " + rs}; files {len(files)}; extra {len(ex)}; changed {len(ch)}; '
      f'missing {len(mi)}; symlinks outside Mathlib {len(links)}; other {len(other)}; Mathlib symlinks {mlinks}; '
      f'Mathlib files {mfiles}; RESULT {"OK" if ok else "FAIL"}')
