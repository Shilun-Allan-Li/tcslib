"""linkcheck.py <out> <snapshot> <queue> <reuse>: rebuilt oleans must have link count 1; reused oleans must be the
snapshot's inode (hard link); no .ilean; no symlink outside Mathlib/; Mathlib/ = symlinks + the NthRootLemmas olean."""
import sys, os, hashlib
out, snap, qf, rf = sys.argv[1:5]
q = [l.strip() for l in open(qf) if l.strip()]; ru = [l.strip() for l in open(rf) if l.strip()]
bad1 = [m for m in q if os.stat(f'{out}/{m}.olean').st_nlink != 1]
badr = [m for m in ru if os.stat(f'{out}/{m}.olean').st_ino != os.stat(f'{snap}/{m}.olean').st_ino]
il, ln, other, ml, mf, n = [], [], [], 0, [], 0
for r, ds, fs in os.walk(out):
    rel = os.path.relpath(r, out); inml = rel == 'Mathlib' or rel.startswith('Mathlib/')
    for f in fs + [x for x in ds if os.path.islink(os.path.join(r, x))]:
        p = os.path.join(r, f); rp = os.path.relpath(p, out)
        if inml:
            if os.path.islink(p): ml += 1
            else: mf.append((rp, hashlib.sha256(open(p, 'rb').read()).hexdigest()))
            continue
        if os.path.islink(p): ln.append(rp)
        elif f.endswith('.ilean'): il.append(rp)
        elif f.endswith('.olean'): n += 1
        else: other.append(rp)
print(f'rebuilt oleans link count 1: {len(q) - len(bad1)}; other: {len(bad1)} {bad1[:5]}')
print(f'reused oleans hard-linked to snapshot: {len(ru) - len(badr)}; not: {len(badr)} {badr[:5]}')
print(f'oleans outside Mathlib/: {n}; .ilean {len(il)}; symlinks outside Mathlib/ {len(ln)}; other files {other}')
print(f'Mathlib/: symlinks {ml}; regular files {mf}')
