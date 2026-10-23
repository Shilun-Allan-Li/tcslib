import sys, zipfile, hashlib, os
zp, root = sys.argv[1], sys.argv[2]
z = zipfile.ZipFile(zp)
bad = []
for i in z.infolist():
    n = i.filename
    if n.startswith('/') or '..' in n.split('/') or '\\' in n:
        bad.append(n)
    mode = (i.external_attr >> 16)
    if (mode & 0o170000) == 0o120000:
        bad.append('symlink:' + n)
print('entries', len(z.infolist()), 'unsafe', bad)
print('testzip', z.testzip())
if not bad and len(sys.argv) > 3 and sys.argv[3] == 'extract':
    z.extractall(root)
# compare
for i in z.infolist():
    if i.is_dir(): continue
    p = os.path.join(root, i.filename)
    d = z.read(i.filename)
    with open(p, 'rb') as f: e = f.read()
    print(('OK ' if d == e else 'DIFF ') + hashlib.sha256(d).hexdigest() + '  ' + i.filename)
