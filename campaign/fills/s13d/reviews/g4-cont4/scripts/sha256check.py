import sys, hashlib, os, zipfile
root, zpath = sys.argv[1], sys.argv[2]
lines = open(os.path.join(root, 'SHA256SUMS'), encoding='utf-8').read().splitlines()
listed = {}
ok = bad = 0
for ln in lines:
    if not ln.strip(): continue
    h, name = ln.split(None, 1)
    name = name.lstrip('*').strip()
    if name.startswith('./'): name = name[2:]
    p = os.path.join(root, name)
    listed[name] = h
    if not os.path.isfile(p):
        print('MISSING', name); bad += 1; continue
    d = hashlib.sha256(open(p, 'rb').read()).hexdigest()
    if d == h: ok += 1
    else: print('BAD', name, h, d); bad += 1
files = []
for dp, dn, fn in os.walk(root):
    for f in fn:
        rel = os.path.relpath(os.path.join(dp, f), root)
        files.append(rel)
unlisted = sorted(f for f in files if f not in listed and f != 'SHA256SUMS')
print(f'listed={len(listed)} ok={ok} bad={bad} files_on_disk={len(files)} unlisted={unlisted}')
z = zipfile.ZipFile(zpath)
names = z.namelist()
print('zip entries', len(names), 'testzip', z.testzip())
unsafe = [n for n in names if n.startswith('/') or '..' in n.split('/')]
print('unsafe names', unsafe)
links = [i.filename for i in z.infolist() if (i.external_attr >> 16) & 0o170000 == 0o120000]
print('symlinks', links)
# byte-equality of members vs extraction
neq = 0
base = os.path.dirname(root)
for i in z.infolist():
    if i.is_dir(): continue
    p = os.path.join(base, i.filename)
    if open(p, 'rb').read() != z.read(i.filename): neq += 1; print('DIFF', i.filename)
print('members differing from extraction', neq)
