import sys, zipfile, hashlib, os, stat
z = zipfile.ZipFile(sys.argv[1]); root = sys.argv[2]
bad = 0
for i in z.infolist():
    n = i.filename
    mode = (i.external_attr >> 16)
    if n.startswith('/') or '..' in n.split('/') or stat.S_ISLNK(mode):
        print('UNSAFE', n); bad += 1; continue
    if n.endswith('/'): continue
    data = z.read(i)
    p = os.path.join(root, n)
    with open(p, 'rb') as f: d2 = f.read()
    print(('SAME ' if d2 == data else 'DIFF ') + hashlib.sha256(data).hexdigest()[:16], n)
    if d2 != data: bad += 1
print('testzip:', z.testzip()); print('bad', bad)
