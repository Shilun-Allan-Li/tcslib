"""Seal test: wrap everything between `namespace Turing` and `end Turing` of the module in a
section that makes the named other-file definitions `local irreducible` (and erases the simp
unfolding of the `@[simp]` definitions among them).
usage: python3 -I mkseal.py <module> <out> <control 0|1|2> <names file> [<-simp names, comma>]
control 1: add, at the top of the sealed section, examples that close only by unfolding a sealed
  definition (each must fail under the seal).
control 2: the same examples with no seal at all (each must succeed: the examples are valid).
"""
import sys

src, out, ctrl, nf = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
nosimp = [n for n in (sys.argv[5].split(',') if len(sys.argv) > 5 else []) if n]
names = [l.strip() for l in open(nf, encoding='utf-8') if l.strip()]
L = open(src, encoding='utf-8').read().split('\n')
s = L.index('namespace Turing') + 1
e = max(i for i, l in enumerate(L) if l == 'end Turing')
att = (['attribute [-simp] ' + ' '.join(nosimp)] if nosimp else []) + \
    ['attribute [local irreducible] ' + n for n in names]
body = L[s:e]
controls = [
    '/-- Seal control 1: closes only by unfolding `Turing.MultiTapeTM.runFrom`. -/',
    'example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) :',
    '    tm.runFrom c 0 = c := rfl', '',
    '/-- Seal control 2: closes only by unfolding `Turing.FinTM.bufferTape`. -/',
    'example : FinTM.bufferTape [true] 0 = some true := by rfl', '',
    '/-- Seal control 3: closes only by unfolding `Turing.counterLoopCfg`. -/',
    'example {k : ℕ} {S : Type} {x : List Bool} (q : Option (CounterLoopState S))',
    '    (c : Cfg k Bool S x) (ct : ℤ → Option Bool) (cp : ℤ) :',
    '    (counterLoopCfg q c ct cp).state = q := rfl', '',
    '/-- Seal control 4: closes only by unfolding `Turing.embedEmitCfg`. -/',
    'example {m k : ℕ} {S : Type} {x : List Bool} (ι : Fin m ↪ Fin k)',
    '    (t : Fin k → ℤ → Option Bool) (h : Fin k → ℤ) (c : Cfg m Bool S x) :',
    '    (embedEmitCfg ι t h [] c).state = c.state := rfl', '']
if ctrl in (1, 2):
    body = controls + body
if ctrl == 2:
    att = []
L = L[:s] + ['section IWSeal'] + att + [''] + body + ['end IWSeal', ''] + L[e:]
open(out, 'w', encoding='utf-8').write('\n'.join(L))
print('sealed lines %d..%d of %s with %d names (-simp: %s); control %s'
      % (s + 1, e, src.split('/')[-1], 0 if ctrl == 2 else len(names), nosimp if ctrl != 2 else [],
         ctrl))
