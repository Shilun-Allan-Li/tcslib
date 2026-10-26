import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import df3lib, df4lib
root = sys.argv[1]
tot = 0
for dp, dn, fn in os.walk(root):
    for f in sorted(fn):
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f); t = open(p).read()
        c3 = df3lib.chunks(t); c4 = df4lib.chunks(t)
        assert len(c3) == len(c4), p
        cnt = collections.Counter(n for n, _, _ in c3)
        dup = {n: k for n, k in cnt.items() if k > 1}
        # v4 names still needing #k
        h = [n for n, _, _ in c4 if '#' in n]
        if dup:
            tot += 1
            print(os.path.relpath(p, root), 'chunks', len(c3), 'v3-distinct', len(cnt), 'collisions', dict(sorted(dup.items())), 'v4#k', h)
print('files with collisions:', tot)
