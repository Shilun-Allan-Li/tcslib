import sys
# usage: mkseal.py <module> <out> <control 0|1> <names...>: wraps the runner home (from the first
# line after `/-! ### The runner -/` to the line before the target's docstring) in a section that
# makes the named other-file definitions `local irreducible`. With control 1, a deliberately
# unfolding example is added inside the section (it must fail).
src, out, ctrl, names = sys.argv[1], sys.argv[2], sys.argv[3] == '1', sys.argv[4:]
L = open(src, encoding='utf-8').read().split('\n')
s = L.index('/-! ### The runner -/') + 1
e = next(i for i, l in enumerate(L) if l.startswith('/-- **H3 with the configuration-count clock**'))
att = 'attribute [local irreducible] ' + ' '.join(names)
body = L[s:e]
if ctrl:
    body = ['/-- Seal control: closes only by unfolding `FinTM.bufferTape`. -/',
            'example : FinTM.bufferTape [true] 0 = some true := by rfl', ''] + body
L = L[:s] + ['section F3C1Seal', att, ''] + body + ['end F3C1Seal', ''] + L[e:]
open(out, 'w', encoding='utf-8').write('\n'.join(L))
print('sealed lines %d..%d of %s with %d names; control %s' % (s + 1, e, src.split('/')[-1], len(names), ctrl))
