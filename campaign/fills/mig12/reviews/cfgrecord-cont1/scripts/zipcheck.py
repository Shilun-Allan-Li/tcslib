import sys, zipfile, hashlib, os, stat
zp, outdir = sys.argv[1], sys.argv[2]
z = zipfile.ZipFile(zp)
bad = []
names = []
for i in z.infolist():
    n = i.filename
    names.append(n)
    mode = (i.external_attr >> 16) & 0xFFFF
    if n.startswith('/') or '..' in n.split('/') or '\\' in n:
        bad.append(('unsafe path', n))
    if stat.S_ISLNK(mode):
        bad.append(('symlink', n))
print('entries', len(names))
print('unsafe', bad)
print('testzip (CRC):', z.testzip())
dups = [n for n in set(names) if names.count(n) > 1]
print('duplicate names', dups)
# compare extracted files
mism = []
for i in z.infolist():
    if i.is_dir():
        continue
    p = os.path.join(outdir, i.filename)
    if not os.path.isfile(p):
        mism.append(('missing', i.filename)); continue
    if open(p,'rb').read() != z.read(i.filename):
        mism.append(('differs', i.filename))
# extra files on disk
ondisk = []
for root, ds, fs in os.walk(outdir):
    for f in fs:
        rel = os.path.relpath(os.path.join(root, f), outdir)
        ondisk.append(rel)
extra = sorted(set(ondisk) - set(n for n in names))
print('mismatches', mism)
print('extra on disk', extra)
