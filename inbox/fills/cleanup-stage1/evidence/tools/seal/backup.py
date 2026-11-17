"""backup.py <tree> <bkdir> <snapshot> <module>...: before a module's olean in <tree> is rebuilt,
copy it (once) to <bkdir> and check its SHA-256 against <snapshot>; modules with no olean in the
snapshot are recorded as NEW (to be deleted at restore). Appends to <bkdir>/backup-log.txt."""
import sys, os, shutil, hashlib
tree, bk, snap, *mods = sys.argv[1:]
ref = dict((l.split('  ',1)[1].rstrip('\n'), l.split('  ',1)[0]) for l in open(snap))
log = open(os.path.join(bk, 'backup-log.txt'), 'a')
for m in mods:
    rel = m.replace('.', '/') + '.olean'
    dst = os.path.join(bk, rel)
    if os.path.exists(dst): continue
    if rel not in ref:
        if not os.path.exists(os.path.join(bk, 'NEW-' + m)):
            open(os.path.join(bk, 'NEW-' + m), 'w').close(); log.write(f'NEW {rel}\n')
        continue
    src = os.path.join(tree, rel)
    h = hashlib.sha256(open(src, 'rb').read()).hexdigest()
    os.makedirs(os.path.dirname(dst), exist_ok=True); shutil.copy2(src, dst)
    h2 = hashlib.sha256(open(dst, 'rb').read()).hexdigest()
    ok = 'OK' if h == ref[rel] == h2 else 'MISMATCH'
    log.write(f'BACKUP {ok} {h2} {rel}\n'); print('BACKUP', ok, rel)
