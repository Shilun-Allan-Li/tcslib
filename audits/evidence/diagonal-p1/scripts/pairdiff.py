import re, sys
# usage: pairdiff.py <head screen> <earlier screen>...  -- pairs (by declaration names) in the head screen absent from
# every earlier screen, and pairs in earlier screens absent from the head.
P = re.compile(r'^\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%')
def pairs(p):
    d = {}
    for l in open(p, encoding='utf-8'):
        m = P.match(l)
        if m: d[(m.group(1), m.group(2))] = l.strip()
    return d
head = pairs(sys.argv[1]); earlier = {}
for p in sys.argv[2:]: earlier.update(pairs(p))
new = [head[k] for k in head if k not in earlier]
gone = [earlier[k] for k in earlier if k not in head]
print(f'head pairs {len(head)}; union of earlier {len(earlier)}; new at head {len(new)}; earlier-only {len(gone)}')
for l in new: print('  NEW  ', l)
for l in gone: print('  GONE ', l)
