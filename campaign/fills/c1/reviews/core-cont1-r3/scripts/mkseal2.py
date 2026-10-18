"""Seal test for the private home: wrap the lines between the replay canonizer's `sorry` and the
target's docstring in a section that makes the named other-file definitions `local irreducible`
(and, with simpseal, erases the simp-unfoldable ones from the simp set).
usage: python3 -I mkseal2.py <module> <out> <seal 0|1> <simpseal 0|1> <controls 0|1> <names file> <simp names file>
With controls 1, four deliberately unfolding examples are added at the start and the same four at
the end of the section (each must fail when sealed and succeed unsealed)."""
import sys
src, out = sys.argv[1], sys.argv[2]
seal, simpseal, ctrl = (a == '1' for a in sys.argv[3:6])
names = [l.strip() for l in open(sys.argv[6], encoding='utf-8') if l.strip()]
snames = [l.strip() for l in open(sys.argv[7], encoding='utf-8') if l.strip()]
L = open(src, encoding='utf-8').read().split('\n')
s = L.index('    ∃ (M : FinTM Bool) (T : ℕ → ℕ),') + 3   # line after `  sorry` of the replay canonizer
assert L[s - 1] == '  sorry' and L[s] == '', (L[s - 1], L[s])
e = next(i for i, l in enumerate(L) if l.startswith('/-- **The interpreter core'))
def controls(tag):
    return [f'/-- Seal control {tag}1: closes only by unfolding `Turing.MultiTapeTM.runFrom`. -/',
            'example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) :',
            '    tm.runFrom c 0 = c := rfl', '',
            f'/-- Seal control {tag}2: closes only by unfolding `Turing.FinTM.bufferTape`. -/',
            'example : FinTM.bufferTape [true] 0 = some true := rfl', '',
            f'/-- Seal control {tag}3: closes only by unfolding `Turing.counterLoopCfg`. -/',
            'example (c : Cfg 2 Bool Unit [true]) (q : Option (CounterLoopState Unit)) :',
            '    (counterLoopCfg q c (fun _ => none) 0).state = q := rfl', '',
            f'/-- Seal control {tag}4: closes only by simp unfolding the `@[simp]` definition `Turing.MultiTapeTM.initCfg`. -/',
            'example {k : ℕ} {S : Type} (tm : MultiTapeTM k Bool S) (x : List Bool) :',
            '    (tm.initCfg x).state = some tm.q₀ := by simp', '']
head = ['section ICSeal']
if seal: head += ['attribute [local irreducible] ' + n for n in names]
if simpseal: head += ['attribute [-simp] ' + ' '.join(snames)]
head += ['']
body = L[s:e]
if ctrl: body = controls('A') + body + controls('Z')
L = L[:s] + head + body + ['end ICSeal', ''] + L[e:]
open(out, 'w', encoding='utf-8').write('\n'.join(L))
print('sealed lines %d..%d with %d irreducible names, %d simp erasures; controls %s' % (s + 1, e, len(names) if seal else 0, len(snames) if simpseal else 0, ctrl))
