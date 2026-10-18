import sys
# usage: mkseal.py <module> <out> <names...>: wraps the delivered private block and target 1 (from
# `/-- The forward state` to the line before target 2's docstring) in a section that makes the
# named other-file definitions `local irreducible`.
src, out, names = sys.argv[1], sys.argv[2], sys.argv[3:]
L = open(src, encoding='utf-8').read().split('\n')
att = 'attribute [local irreducible] ' + ' '.join(names)
s = next(i for i, l in enumerate(L) if l.startswith('/-- The forward state'))
e = next(i for i, l in enumerate(L) if l.startswith('/-- **H5, the ruler device\'s call rows**'))
L = L[:e] + ['end B6F5Seal', ''] + L[e:]
L = L[:s] + ['section B6F5Seal', att, ''] + L[s:]
open(out, 'w', encoding='utf-8').write('\n'.join(L)); print('sealed', len(names), 'definitions; section at line', s + 1, 'to', e + 3)
