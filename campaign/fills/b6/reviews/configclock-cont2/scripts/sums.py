import hashlib, os, sys, zipfile
# usage: sums.py <zip> <extracted root dir> : verify SHA256SUMS inside root; compare every zip member to the extraction
zp, root = sys.argv[1], sys.argv[2]
z = zipfile.ZipFile(zp)
bad = z.testzip()
print('zip testzip:', 'OK' if bad is None else 'BAD ' + bad)
names = [i.filename for i in z.infolist()]
print('entries:', len(names), 'files:', sum(1 for n in names if not n.endswith('/')))
unsafe = [n for n in names if n.startswith('/') or '..' in n.split('/')]
print('unsafe names:', unsafe)
for i in z.infolist():
    mode = (i.external_attr >> 16) & 0o170000
    if mode == 0o120000: print('SYMLINK entry:', i.filename)
base = os.path.dirname(root.rstrip('/'))
mism = 0
for n in names:
    if n.endswith('/'): continue
    p = os.path.join(base, n)
    if open(p, 'rb').read() != z.read(n): mism += 1; print('MISMATCH', n)
print('members byte-equal to extraction:', 'all' if mism == 0 else f'{mism} mismatches')
ok = fail = 0; listed = set()
for line in open(os.path.join(root, 'SHA256SUMS'), encoding='utf-8'):
    line = line.rstrip('\n')
    if not line.strip(): continue
    h, f = line.split(None, 1); f = f.lstrip('*').strip()
    listed.add(f)
    p = os.path.join(root, f)
    if not os.path.exists(p): print('MISSING', f); fail += 1; continue
    if hashlib.sha256(open(p, 'rb').read()).hexdigest() == h: ok += 1
    else: print('FAIL', f); fail += 1
print(f'SHA256SUMS: {ok} OK, {fail} failed, {len(listed)} listed')
pref = os.path.basename(root.rstrip('/')) + '/'
files = {n[len(pref):] for n in names if not n.endswith('/') and n.startswith(pref)}
print('members not listed (except SHA256SUMS):', sorted(files - listed - {'SHA256SUMS'}))
print('listed but not members:', sorted(listed - files))
