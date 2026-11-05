"""Verify a SHA256SUMS file against a directory; list files present but not listed (python3 -I).
usage: python3 -I sumscheck.py <root>"""
import hashlib, os, sys
root = sys.argv[1]
listed = {}
for l in open(os.path.join(root, 'SHA256SUMS'), encoding='utf-8'):
    l = l.rstrip('\n')
    if not l.strip(): continue
    h, p = l.split(None, 1); p = os.path.normpath(p.lstrip('*'))
    listed[p] = h
ok = bad = missing = 0; bads = []
for p, h in listed.items():
    fp = os.path.join(root, p)
    if not os.path.exists(fp): missing += 1; bads.append('MISSING ' + p); continue
    if hashlib.sha256(open(fp, 'rb').read()).hexdigest() == h: ok += 1
    else: bad += 1; bads.append('BAD ' + p)
present = set()
for dp, dn, fn in os.walk(root):
    for f in fn: present.add(os.path.relpath(os.path.join(dp, f), root))
unlisted = sorted(present - set(listed) - {'SHA256SUMS'})
print(f'entries {len(listed)} ok {ok} bad {bad} missing {missing}')
for b in bads: print(' ', b)
print('unlisted files:', unlisted)
