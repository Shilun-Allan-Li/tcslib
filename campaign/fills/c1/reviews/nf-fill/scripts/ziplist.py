"""List a zip's members with sizes, timestamps, and flags unsafe paths/symlinks (python3 -I).
usage: python3 -I ziplist.py <zip>"""
import sys, zipfile, stat
z = zipfile.ZipFile(sys.argv[1])
bad = []
for i in z.infolist():
    mode = (i.external_attr >> 16) & 0o177777
    link = stat.S_ISLNK(mode)
    n = i.filename
    unsafe = n.startswith('/') or '..' in n.split('/') or link
    if unsafe: bad.append(n)
    print(f"{'%04d-%02d-%02d %02d:%02d:%02d' % i.date_time} {i.file_size:>9} {'LINK ' if link else ''}{n}")
print('members', len(z.infolist()), 'unsafe', bad)
