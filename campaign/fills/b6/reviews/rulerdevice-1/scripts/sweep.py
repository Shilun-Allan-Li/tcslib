import re, sys
# usage: sweep.py <log> <order list>: CHECK order vs the order list; sorry warnings per module
log = open(sys.argv[1], encoding='utf-8', errors='replace').read().split('\n')
order = [l.strip() for l in open(sys.argv[2], encoding='utf-8') if l.strip() and not l.startswith('#')]
checks = [re.sub(r'^\d+/\d+ ', '', l.split(None, 1)[1].strip()) for l in log if l.startswith('CHECK ')]
mods = [c for c in checks if c.startswith('TCSlib')]
print('CHECK lines', len(checks), '; TCSlib modules', len(mods), '; order list', len(order))
print('module CHECK sequence == order list:', mods == order, '| first divergence:', next(((i, a, b) for i, (a, b) in enumerate(zip(mods, order)) if a != b), None))
print('non-module CHECKs:', [c for c in checks if not c.startswith('TCSlib')])
per = {}
for l in log:
    m = re.match(r"^(TCSlib/\S+)\.lean:(\d+):\d+: warning: declaration uses 'sorry'", l)
    if m: per.setdefault(m.group(1), set()).add(int(m.group(2)))
print('sorry warnings: %d in %d modules' % (sum(len(v) for v in per.values()), len(per)))
for k in sorted(per): print('  ', k.replace('TCSlib/Complexity/', ''), len(per[k]), sorted(per[k]))
print('errors:', [l for l in log if re.search(r':\d+:\d+: error', l)][:5])
print('PASS lines', sum(l.startswith('PASS ') for l in log), '; tail:', [l for l in log if 'SWEEP' in l or 'BOOTSTRAP' in l][-3:])
