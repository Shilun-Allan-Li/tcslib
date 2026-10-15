import sys, re
def pairs(p):
    out = {}
    for l in open(p):
        m = re.match(r'\s+(\S+)\s+reproduces\s+(\S+):\s*(\S+)\s*=\s*(\d+)%', l)
        if m: out[(m.group(1), m.group(2))] = (m.group(3), int(m.group(4)))
    return out
a = pairs(sys.argv[1]); b = pairs(sys.argv[2])
new = sorted(set(b) - set(a))
cross = [p for p in new if p[0].split('::')[0] != p[1].split('::')[0]]
print(f'  before {len(a)} pairs, after {len(b)}; new {len(new)} (cross-file {len(cross)}); gone {len(set(a)-set(b))}')
for p in cross: print('   CROSS', p[0], '<-', p[1], b[p][0], f'{b[p][1]}%')
for p in new:
    if p not in cross: print('   in-file', p[0], '<-', p[1], b[p][0], f'{b[p][1]}%')
