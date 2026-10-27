"""Extract a zip into an empty directory (regular files only, mode 0644) (python3 -I).
usage: python3 -I zipextract.py <zip> <dest>"""
import os, sys, zipfile
z = zipfile.ZipFile(sys.argv[1]); dest = os.path.realpath(sys.argv[2])
os.makedirs(dest, exist_ok=True)
n = 0
for i in z.infolist():
    if i.is_dir(): continue
    p = os.path.realpath(os.path.join(dest, i.filename))
    assert p.startswith(dest + os.sep), p
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with z.open(i) as src, open(p, 'wb') as out: out.write(src.read())
    os.chmod(p, 0o644); n += 1
print('extracted', n, 'files into', dest)
