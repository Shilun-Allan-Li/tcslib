"""Report each token as resolved (first candidate whose #check line has no error) or not."""
import sys, re, collections
mapf, logs = sys.argv[1], sys.argv[2:]
err = set()
for lg in logs:
    for l in open(lg, encoding='utf-8'):
        m = re.search(r'([^/\s]+\.lean):(\d+):\d+: error', l)
        if m: err.add((m.group(1), int(m.group(2))))
res = collections.OrderedDict()
for l in open(mapf, encoding='utf-8'):
    fn, n, t, c = l.rstrip('\n').split('\t')
    res.setdefault(t, None)
    if res[t] is None and (fn.split('/')[-1], int(n)) not in err:
        res[t] = c
for t, c in res.items():
    print(('OK      ' + c) if c else ('MISSING ' + t))
