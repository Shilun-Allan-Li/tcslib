"""Hit lines of a v3 screen output with at least one side in an added file (by v3's label rule).
usage: python3 -I screenfilter.py <screen.out> <population.txt> <added.txt>"""
import os, re, sys
out, popf, addf = sys.argv[1:4]
pop = [l.strip() for l in open(popf) if l.strip()]
new = {l.strip() for l in open(addf) if l.strip()}
nb = {}
for p in pop: nb[os.path.basename(p)] = nb.get(os.path.basename(p), 0) + 1
lab = {(os.path.basename(p) if nb[os.path.basename(p)] == 1 else p): p for p in pop}
P = re.compile(r'^\s+(\S+?)::(\S+)\s+reproduces\s+(\S+?)::(\S+): (\d+)/(\d+) = (\d+)%$')
for l in open(out, encoding='utf-8'):
    m = P.match(l.rstrip('\n'))
    if m and (lab[m.group(1)] in new or lab[m.group(3)] in new): sys.stdout.write(l)
