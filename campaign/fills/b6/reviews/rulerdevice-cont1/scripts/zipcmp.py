import sys, zipfile, hashlib, os, stat
z = zipfile.ZipFile(sys.argv[1]); root = sys.argv[2]
prefix = sys.argv[3] if len(sys.argv) > 3 else ''
bad = 0; n_files = 0
names = set()
for i in z.infolist():
    n = i.filename
    mode = (i.external_attr >> 16)
    if n.startswith('/') or '..' in n.split('/') or stat.S_ISLNK(mode):
        print('UNSAFE', n); bad += 1; continue
    if n.endswith('/'): continue
    n_files += 1
    data = z.read(i)
    rel = n[len(prefix):] if prefix and n.startswith(prefix) else n
    names.add(rel)
    p = os.path.join(root, rel)
    try:
        with open(p, 'rb') as f: d2 = f.read()
    except FileNotFoundError:
        print('MISSING', n); bad += 1; continue
    print(('SAME ' if d2 == data else 'DIFF ') + hashlib.sha256(data).hexdigest()[:16], n)
    if d2 != data: bad += 1
extra = []
for dp, dn, fn in os.walk(root):
    for f in fn:
        rel = os.path.relpath(os.path.join(dp, f), root)
        if rel not in names: extra.append(rel)
print('files in zip:', n_files, 'extra on disk:', sorted(extra))
print('testzip:', z.testzip()); print('bad', bad)
