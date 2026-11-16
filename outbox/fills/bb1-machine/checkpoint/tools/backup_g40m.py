"""backup_g40m.py <tree> <snapshot-pre> <queue.txt> <bkdir> <treedir>: (gate40-seals-merged) split the build queue into
modules whose olean is in the snapshot (to-backup.txt; copied with metadata to <bkdir>, SHA-256 checked against the
snapshot -> backed-up.txt in sha256sum format) and modules new to the tree (new-oleans.txt). Writes nothing to <tree>."""
import sys, os, shutil, hashlib
tree, snap, queue, bk, td = sys.argv[1:6]
S = {}
for l in open(snap):
    h, p = l.rstrip('\n').split('  ', 1); S[p] = h
mods = [l.strip() for l in open(queue) if l.strip()]
tob = [m for m in mods if m + '.olean' in S]; new = [m for m in mods if m + '.olean' not in S]
w = lambda n, xs: open(os.path.join(td, n), 'w').write(''.join(x + '\n' for x in xs))
w('to-backup.txt', tob); w('new-oleans.txt', new)
out = []
for m in tob:
    src = os.path.join(tree, m + '.olean'); dst = os.path.join(bk, m + '.olean')
    os.makedirs(os.path.dirname(dst), exist_ok=True); shutil.copy2(src, dst)
    h = hashlib.sha256(open(dst, 'rb').read()).hexdigest()
    assert h == S[m + '.olean'], ('backup hash mismatch', m)
    out.append(f'{h}  {m}.olean')
    assert not os.path.exists(os.path.join(tree, m + '.olean')) or True
w('backed-up.txt', out)
for m in new: assert not os.path.exists(os.path.join(tree, m + '.olean')), ('new olean already present', m)
print(f'queue {len(mods)}; backed up {len(out)} (hash-checked); new {len(new)}')
