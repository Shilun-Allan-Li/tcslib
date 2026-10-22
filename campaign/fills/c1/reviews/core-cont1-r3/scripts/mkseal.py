"""Seal test: wrap everything between `namespace Turing` and `end Turing` of the module in a
section that makes the named other-file definitions `local irreducible`.
usage: python3 -I mkseal.py <module> <out> <control 0|1> <names file>
With control 1, three deliberately unfolding examples are added at the top of the section (each
must fail)."""
import sys
src, out, ctrl, nf = sys.argv[1], sys.argv[2], sys.argv[3] == '1', sys.argv[4]
names = [l.strip() for l in open(nf, encoding='utf-8') if l.strip()]
L = open(src, encoding='utf-8').read().split('\n')
s = L.index('namespace Turing') + 1
e = max(i for i, l in enumerate(L) if l == 'end Turing')
att = ['attribute [local irreducible] ' + n for n in names]
body = L[s:e]
if ctrl:
    body = ['/-- Seal control 1: closes only by unfolding `Turing.MultiTapeTM.runFrom`. -/',
            'example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) :',
            '    tm.runFrom c 0 = c := rfl', '',
            '/-- Seal control 2: closes only by unfolding `Turing.FinTM.bufferTape`. -/',
            'example : FinTM.bufferTape [true] 0 = some true := by rfl', '',
            '/-- Seal control 3: closes only by unfolding `Turing.NDTM.runWith`. -/',
            'example {k : ℕ} {S : Type} {x : List Bool} (N : NDTM k Bool S) (c : Cfg k Bool S x) :',
            '    N.runWith [] c = c := rfl', ''] + body
L = L[:s] + ['section XRSeal'] + att + [''] + body + ['end XRSeal', ''] + L[e:]
open(out, 'w', encoding='utf-8').write('\n'.join(L))
print('sealed lines %d..%d of %s with %d names; control %s' % (s + 1, e, src.split('/')[-1], len(names), ctrl))
