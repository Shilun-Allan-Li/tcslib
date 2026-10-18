"""New-warning check: compare (message, source line) multisets of two elaboration outputs.

Usage: python3 -I warndiff.py <base.lean> <base.out> <new.lean> <new.out>
A warning is keyed by its first message line and the stripped source line it points at, so moved
code keeps its key; a key whose count grows is a new warning.
"""
import collections, re, sys
def keys(src, out):
    L = open(src, encoding='utf-8').read().split('\n')
    c = collections.Counter()
    for l in open(out, encoding='utf-8').read().split('\n'):
        m = re.match(r'^.*?\.lean:(\d+):(\d+): warning: (.*)$', l)
        if m: c[(m.group(3).strip(), L[int(m.group(1)) - 1].strip())] += 1
    return c
a = keys(sys.argv[1], sys.argv[2]); b = keys(sys.argv[3], sys.argv[4])
print('warnings base/new:', sum(a.values()), sum(b.values()))
new = b - a
print('new warnings:', sum(new.values()))
for (msg, line), n in sorted(new.items()): print(f'  {n}x {msg} @ {line[:90]}')
gone = a - b
print('removed warnings:', sum(gone.values()))
for (msg, line), n in sorted(gone.items()): print(f'  {n}x {msg} @ {line[:90]}')
