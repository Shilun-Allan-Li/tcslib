import sys, zipfile, hashlib, os
# usage: zipcmp.py <zip> <extract dir>: every member byte-equal to its extraction; unsafe names; extra files
z = zipfile.ZipFile(sys.argv[1]); root = sys.argv[2]
names = z.namelist(); bad = z.testzip()
print('members', len(names), 'testzip', bad)
files = [n for n in names if not n.endswith('/')]
unsafe = [n for n in names if n.startswith('/') or '..' in n.split('/')]
print('unsafe', unsafe)
diff = []
for n in files:
    p = os.path.join(root, n)
    if not os.path.isfile(p) or open(p, 'rb').read() != z.read(n): diff.append(n)
print('file members', len(files), 'differing/missing', diff)
on_disk = []
for d, _, fs in os.walk(root):
    for f in fs: on_disk.append(os.path.relpath(os.path.join(d, f), root))
print('extra on disk', sorted(set(on_disk) - set(files)))
