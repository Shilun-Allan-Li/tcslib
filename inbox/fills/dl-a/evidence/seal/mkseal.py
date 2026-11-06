"""mkseal.py SRC OUT NAMESFILE TARGET[:HELPERMARK] ...
Wrap each target (from its helper mark, or its docstring, to the end of its proof) in
`section dlaSeal` with `attribute [local irreducible] <names>`, so that the seal covers
exactly the fill's code."""
import sys
src, out, namesf = sys.argv[1:4]
names = open(namesf).read().split()
s = open(src).read()
blocks = []
for spec in sys.argv[4:]:
    t, _, mark = spec.partition(':')
    ti = s.index('theorem ' + t + ' ')
    start = s.index(mark) if mark else s.rindex('/--', 0, ti)
    assert start <= ti
    j = s.index(':= by\n', ti)
    end = s.index('\n\n', j) + 1
    blocks.append((start, end))
hdr = '\nsection dlaSeal\n-- rule 10 seal (fill dl-a)\nattribute [local irreducible] ' + ' '.join(names) + '\n\n'
for start, end in sorted(blocks, reverse=True):
    s = s[:end] + 'end dlaSeal\n' + s[end:]
    s = s[:start] + hdr.lstrip('\n') + s[start:]
open(out, 'w').write(s)
print('sealed', len(blocks), 'blocks')
