"""Check every package present in .lake/packages against lake-manifest.json (URL, rev)."""
import json, os, subprocess, sys
man = json.load(open('lake-manifest.json'))
ok = True
for p in man['packages']:
    d = os.path.join('.lake/packages', p['name'])
    if not os.path.isdir(d):
        print('ABSENT', p['name']); continue
    url = subprocess.run(['git', '-C', d, 'remote', 'get-url', 'origin'], capture_output=True, text=True).stdout.strip()
    rev = subprocess.run(['git', '-C', d, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    m = (url == p['url'] and rev == p['rev'])
    ok &= m
    print('MATCH' if m else 'MISMATCH', p['name'], url, rev, '' if m else 'expected %s %s' % (p['url'], p['rev']))
order = sys.argv[1]
absent = [p['name'] for p in man['packages'] if not os.path.isdir(os.path.join('.lake/packages', p['name']))]
n = 0
for m in open(order).read().split():
    for line in open(m + '.lean'):
        if line.startswith('import '):
            root = line.split()[1].split('.')[0]
            if root in absent: n += 1; print('ORDER IMPORTS ABSENT', m, line.strip())
print('order imports of absent packages:', n)
print('PASS (all present packages match)' if ok and n == 0 else 'FAIL')
