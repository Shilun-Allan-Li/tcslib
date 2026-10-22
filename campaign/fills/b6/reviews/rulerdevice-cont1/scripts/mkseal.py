"""Seal test for Build/InputDevice: wrap the module body from its first `rd_` declaration (head line
206, the inherited test kit, the two filled rows and their homes) to `end Turing` in a section that
makes the named other-file definitions `local irreducible`, optionally erases the two `@[simp]`
other-file definitions (`Turing.Action.apply`, `Turing.Cfg.init`) from the simp set, with optional
controls at the top and the end of the section. Each control closes only by unfolding one sealed
definition (or, for the simp controls, by simp unfolding an erased `@[simp] def`), so each must
fail sealed and pass unsealed.
usage: python3 -I mkseal.py <module> <out> <names file> <seal 0|1> <simp-erase 0|1> <controls 0|1> [body 0|1]"""
import sys
src, out, nf = sys.argv[1], sys.argv[2], sys.argv[3]
seal, erase, ctrl = sys.argv[4] == '1', sys.argv[5] == '1', sys.argv[6] == '1'
keep = (sys.argv[7] == '1') if len(sys.argv) > 7 else True
names = [l.strip() for l in open(nf, encoding='utf-8') if l.strip()]
L = open(src, encoding='utf-8').read().split('\n')
s = next(i for i, l in enumerate(L) if l.startswith('/-- The forward state'))
e = max(i for i, l in enumerate(L) if l == 'end Turing')
att = (['attribute [local irreducible] ' + n for n in names] if seal else []) + \
      (['attribute [-simp] Turing.Action.apply Turing.Cfg.init'] if erase else [])
def controls(tag):
    C = [
     ('runFrom', 'example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) :\n    tm.runFrom c 0 = c := rfl'),
     ('step', 'example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) :\n    tm.step { c with state := none } = { c with state := none } := rfl'),
     ('visitedByTapeHead', 'example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x)\n    (i : Fin k) : tm.visitedByTapeHead c 0 i = (Finset.range 1).image fun u => (tm.runFrom c u).workTapePos i := rfl'),
     ('Action.apply (simp)', 'example {k : ℕ} {S : Type} {x : List Bool} (a : Action k Bool S) (c : Cfg k Bool S x) :\n    (a.apply c).state = a.state := by simp'),
     ('Action.apply (rfl)', 'example {k : ℕ} {S : Type} {x : List Bool} (a : Action k Bool S) (c : Cfg k Bool S x) :\n    (a.apply c).output = c.output ++ a.output.toList := rfl'),
     ('Action.mapState', 'example {k : ℕ} {S S\' : Type} (f : S → S\') (a : Action k Bool S) :\n    (a.mapState f).state = a.state.map f := rfl'),
     ('Cfg.mapState', 'example {k : ℕ} {S S\' : Type} {x : List Bool} (f : S → S\') (c : Cfg k Bool S x) :\n    (c.mapState f).inputPos = c.inputPos := rfl'),
     ('moveInputPos', 'example : moveInputPos (n := 1) (2 : Fin 3) 1 = 2 := rfl'),
     ('FinTM.bufferTape', 'example : FinTM.bufferTape [true] 0 = some true := by rfl'),
     ('Cfg.inputSymbol', 'example {S : Type} (q : S) :\n    (⟨some q, 0, fun _ _ => none, fun _ => 0, []⟩ : Cfg 1 Bool S [true]).inputSymbol = none := rfl'),
     ('Cfg.workTapeSymbols', 'example {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) (i : Fin k) :\n    c.workTapeSymbols i = c.workTapes i (c.workTapePos i) := rfl'),
     ('Cfg.init (rfl)', 'example {k : ℕ} {S : Type} (q : S) (x : List Bool) :\n    (Cfg.init q x : Cfg k Bool S x).inputPos = 1 := rfl'),
     ('Cfg.init (simp)', 'example {k : ℕ} {S : Type} (q : S) (x : List Bool) :\n    (Cfg.init q x : Cfg k Bool S x).output = [] := by simp'),
     ('tapeAction', 'example {S : Type} (q : S) : (tapeAction (Symbol := Bool) (0 : Fin 1) 0 none 0 q).state = some q := rfl'),
     ('inputMoveAction', 'example {S : Type} (q : S) : (inputMoveAction (k := 1) (Symbol := Bool) 0 q).state = some q := rfl'),
     ('phaseHostTM', 'example {k : ℕ} {I : Type} {Ph : I → Type} (M : (i : I) → MultiTapeTM k Bool (Ph i))\n    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) :\n    (phaseHostTM M q0 red).q₀ = q0 := rfl'),
     ('embedEmitTM', 'example {m k : ℕ} {S : Type} (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S) :\n    (embedEmitTM ι M).q₀ = M.q₀ := rfl'),
     ('embedEmitCfg', 'example {m k : ℕ} {S : Type} {x : List Bool} (ι : Fin m ↪ Fin k) (tapes : Fin k → ℤ → Option Bool)\n    (heads : Fin k → ℤ) (pre : List Bool) (c : Cfg m Bool S x) :\n    (embedEmitCfg ι tapes heads pre c).state = c.state := rfl'),
     ('pairEncode', 'example : pairEncode [] [true] = [false, true, true] := by rfl'),
    ]
    out = []
    for i, (n, body) in enumerate(C):
        out += [f'/-- Control {tag}{i+1}: closes only by unfolding `{n}`. -/', body, '']
    return out
body = L[s:e] if keep else []
if ctrl: body = controls('top-') + body + controls('end-')
L = L[:s] + ['section F5Seal'] + att + [''] + body + ['end F5Seal', ''] + L[e:]
open(out, 'w', encoding='utf-8').write('\n'.join(L))
print('wrote %s: seal %s (%d names), simp-erase %s, controls %s, body %s; body starts at source line %d' % (out.split('/')[-1], seal, len(names), erase, ctrl, keep, s + 1))
