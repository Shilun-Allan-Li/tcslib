"""restoreplan.py <tree> <snapshot-ref> <base-order> <outdir> [--delete]: compare every file under <tree> with the
reference snapshot (treecheck.py format). Writes extra.txt (files absent from the snapshot, with SHA-256), changed.txt
(files whose hash differs, with both hashes), missing.txt, and rebuild-order.txt (the changed .olean modules in
<base-order> order, imports first). With --delete, removes the extra files and then any directory left empty."""
import sys, os, hashlib
tree, ref, order, outd = sys.argv[1:5]; dele = '--delete' in sys.argv
os.makedirs(outd, exist_ok=True)
R = {}
for l in open(ref):
    h, p = l.rstrip('\n').split('  ', 1); R[p] = h
F = {}
for d, ds, fs in os.walk(tree):
    for f in fs:
        p = os.path.join(d, f); F[os.path.relpath(p, tree)] = hashlib.sha256(open(p, 'rb').read()).hexdigest()
extra = sorted(p for p in F if p not in R); changed = sorted(p for p in F if p in R and F[p] != R[p]); missing = sorted(p for p in R if p not in F)
open(os.path.join(outd, 'extra.txt'), 'w').write(''.join(f'{F[p]}  {p}\n' for p in extra))
open(os.path.join(outd, 'changed.txt'), 'w').write(''.join(f'{R[p]} -> {F[p]}  {p}\n' for p in changed))
open(os.path.join(outd, 'missing.txt'), 'w').write(''.join(f'{R[p]}  {p}\n' for p in missing))
mods = [l.strip() for l in open(order) if l.strip()]
ch = {p[:-6] for p in changed if p.endswith('.olean')}
other = [p for p in changed if not p.endswith('.olean')]
reb = [m for m in mods if m in ch]; notin = sorted(ch - set(reb))
open(os.path.join(outd, 'rebuild-order.txt'), 'w').write(''.join(m + '\n' for m in reb))
print(f'files {len(F)}; extra {len(extra)}; changed {len(changed)} (non-olean {len(other)}); missing {len(missing)}; rebuild {len(reb)}; changed oleans not in base order {notin}')
if dele:
    for p in extra: os.remove(os.path.join(tree, p))
    gone = []
    for d, ds, fs in sorted(os.walk(tree), key=lambda x: -len(x[0])):
        if d != tree and not os.listdir(d): os.rmdir(d); gone.append(os.path.relpath(d, tree))
    open(os.path.join(outd, 'deleted-dirs.txt'), 'w').write(''.join(g + '\n' for g in gone))
    print(f'deleted {len(extra)} files and {len(gone)} emptied directories')
