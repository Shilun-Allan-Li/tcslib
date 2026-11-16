"""restore.py <tree> <bkdir> <snapshot-pre> <log>: copy every backup back (checking its hash against
the snapshot), delete every olean not in the snapshot, prune emptied directories, and write the
log. The snapshot comparison itself is done by snapshot.py afterwards."""
import sys, os, shutil, hashlib
tree, bk, snap, logp = sys.argv[1:]
ref = dict((l.split('  ',1)[1].rstrip('\n'), l.split('  ',1)[0]) for l in open(snap))
log = open(logp, 'w'); fails = 0; nrest = 0; ndel = 0
for d, _, fs in os.walk(bk):
    for f in fs:
        if not f.endswith('.olean'): continue
        src = os.path.join(d, f); rel = os.path.relpath(src, bk)
        h = hashlib.sha256(open(src, 'rb').read()).hexdigest()
        if h != ref.get(rel): fails += 1; log.write(f'HASH-FAIL {rel}\n'); continue
        shutil.copy2(src, os.path.join(tree, rel)); nrest += 1; log.write(f'RESTORED {rel}\n')
for d, _, fs in os.walk(tree):
    for f in fs:
        rel = os.path.relpath(os.path.join(d, f), tree)
        if rel not in ref: os.remove(os.path.join(tree, rel)); ndel += 1; log.write(f'DELETED {rel}\n')
pruned = 0
for d, ds, fs in sorted(os.walk(tree), key=lambda t: -len(t[0])):
    if d != tree and not os.listdir(d): os.rmdir(d); pruned += 1; log.write(f'PRUNED {os.path.relpath(d, tree)}\n')
log.write(f'restored {nrest} hash-failures {fails} deleted {ndel} pruned {pruned}\n')
print(f'restored {nrest} hash-failures {fails} deleted {ndel} pruned {pruned}')
