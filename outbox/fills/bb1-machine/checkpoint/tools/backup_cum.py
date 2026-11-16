"""backup_cum.py <tree> <snapshot-pre> <queue.txt> <bkdir> <treedir> (fill-pair-bdh; cumulative form of gate40-seals-merged's
backup_g40m.py): before a build of <queue.txt> on <tree>, copy (with metadata) every queued module whose olean is in the
snapshot and not yet backed up to <bkdir>, SHA-256-checked against the snapshot, appending `<sha256>  <m>.olean` to
<treedir>/backed-up.txt; append queued modules new to the tree (not in the snapshot) to <treedir>/new-oleans.txt.
A module already backed up is skipped (its backup is the snapshot copy). Writes nothing to <tree>."""
import sys, os, shutil, hashlib
tree, snap, queue, bk, td = sys.argv[1:6]
S = {}
for l in open(snap):
    h, p = l.rstrip('\n').split('  ', 1); S[p] = h
rd = lambda n: [l.strip() for l in open(os.path.join(td, n))] if os.path.exists(os.path.join(td, n)) else []
done = {l.split('  ', 1)[1][:-6] for l in rd('backed-up.txt') if l}; newd = set(rd('new-oleans.txt'))
mods = [l.strip() for l in open(queue) if l.strip()]
nb = nn = 0
with open(os.path.join(td, 'backed-up.txt'), 'a') as fb, open(os.path.join(td, 'new-oleans.txt'), 'a') as fn:
    for m in mods:
        if m + '.olean' in S:
            if m in done: continue
            src = os.path.join(tree, m + '.olean'); dst = os.path.join(bk, m + '.olean')
            assert hashlib.sha256(open(src, 'rb').read()).hexdigest() == S[m + '.olean'], ('tree olean differs from snapshot before backup', m)
            os.makedirs(os.path.dirname(dst), exist_ok=True); shutil.copy2(src, dst)
            h = hashlib.sha256(open(dst, 'rb').read()).hexdigest()
            assert h == S[m + '.olean'], ('backup hash mismatch', m)
            fb.write(f'{h}  {m}.olean\n'); done.add(m); nb += 1
        else:
            if m in newd: continue
            fn.write(m + '\n'); newd.add(m); nn += 1
print(f'queue {len(mods)}; newly backed up {nb} (hash-checked); total backed up {len(done)}; newly listed new {nn}; total new {len(newd)}')
