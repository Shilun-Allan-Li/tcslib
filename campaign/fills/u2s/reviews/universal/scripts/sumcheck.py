import sys, hashlib, os
root, sums = sys.argv[1], sys.argv[2]
ok = bad = missing = 0
listed = set()
for line in open(sums, encoding='utf-8'):
    line = line.rstrip('\n')
    if not line: continue
    h, p = line.split(None, 1)
    p = p.lstrip('*').strip()
    if p.startswith('./'): p = p[2:]
    listed.add(os.path.normpath(p))
    fp = os.path.join(root, p)
    if not os.path.isfile(fp):
        missing += 1; print('MISSING', p); continue
    d = hashlib.sha256(open(fp,'rb').read()).hexdigest()
    if d == h: ok += 1
    else: bad += 1; print('BAD', p)
allf = set()
for dp, dn, fn in os.walk(root):
    for f in fn:
        allf.add(os.path.normpath(os.path.relpath(os.path.join(dp,f), root)))
unlisted = sorted(allf - listed)
print('entries', len(listed), 'ok', ok, 'bad', bad, 'missing', missing)
print('files on disk', len(allf), 'unlisted', unlisted)
