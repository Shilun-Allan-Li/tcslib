"""snapshot.py <tree> <out>: SHA-256 of every file under <tree>, sorted by relative path, in the
`<sha256>  <relpath>` form of treecheck.py's snapshot; prints the file count, the empty
directories and the snapshot's own SHA-256."""
import sys, os, hashlib
tree, out = sys.argv[1:3]
sha = lambda b: hashlib.sha256(b).hexdigest()
files = {}
for d, ds, fs in os.walk(tree):
    for f in fs:
        p = os.path.join(d, f)
        with open(p, 'rb') as h:
            files[os.path.relpath(p, tree)] = sha(h.read())
empty = sorted(os.path.relpath(d, tree) for d, ds, fs in os.walk(tree) if not ds and not fs)
with open(out, 'w') as o:
    for f in sorted(files):
        o.write(f'{files[f]}  {f}\n')
with open(out, 'rb') as h:
    digest = sha(h.read())
print(f'files {len(files)}; empty dirs {len(empty)} {empty[:5]}; snapshot sha256 {digest}')
