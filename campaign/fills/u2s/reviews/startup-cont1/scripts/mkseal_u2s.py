"""Seal test for UniversalK (U2-S cont1): wrap the body between `namespace Turing` and the last
`end Turing` in a section that makes the named other-file definitions `local irreducible` (and
optionally erases the three `@[simp]` definitions from the simp set), with optional controls at
the top and the end of the section. Each control closes only by unfolding one sealed definition,
so each must fail when sealed and pass unsealed.
usage: python3 -I mkseal_u2s.py <module> <out> <names file> <seal 0|1> <erase 0|1> <controls 0|1> [body 0|1]"""
import sys
src, out, nf = sys.argv[1], sys.argv[2], sys.argv[3]
seal, erase, ctrl = sys.argv[4] == '1', sys.argv[5] == '1', sys.argv[6] == '1'
keep = (sys.argv[7] == '1') if len(sys.argv) > 7 else True
names = [l.strip() for l in open(nf, encoding='utf-8') if l.strip()]
L = open(src, encoding='utf-8').read().split('\n')
s = L.index('namespace Turing') + 1
e = max(i for i, l in enumerate(L) if l == 'end Turing')
SIMPDEFS = ['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg']
att = (['attribute [local irreducible] ' + n for n in names] if seal else []) + \
      (['attribute [-simp] ' + n for n in SIMPDEFS] if erase else [])
def controls(tag):
    C = [
      ('runFrom', 'example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) :\n    tm.runFrom c 0 = c := rfl'),
      ('bufferTape', 'example : FinTM.bufferTape [true] 0 = some true := by rfl'),
      ('mapState', "example {k : ℕ} {S S' : Type} {x : List Bool} (f : S → S') (c : Cfg k Bool S x) :\n    (c.mapState f).inputPos = c.inputPos := rfl"),
      ('skipTM', 'example {k : ℕ} (i : Fin k) : (skipTM (Symbol := Bool) k i).q₀ = .run := rfl'),
      ('skipBackTM', 'example {k : ℕ} (i : Fin k) : (skipBackTM (Symbol := Bool) k i).q₀ = .run := rfl'),
      ('clearTM', 'example {k : ℕ} (i : Fin k) : (clearTM (Symbol := Bool) k i).q₀ = .sweep := rfl'),
      ('pairEncode', 'example : pairEncode [] [true] = [false, true, true] := by rfl'),
      ('seamCompTM', 'example {k : ℕ} {S₁ S₂ : Type} [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁) (e : S₁)\n    (M₂ : MultiTapeTM k Bool S₂) (q : S₂) : (seamCompTM M₁ e M₂ q).q₀ = Sum.inl M₁.q₀ := rfl'),
      ('initCfg', 'example {k : ℕ} {S : Type} (tm : MultiTapeTM k Bool S) (x : List Bool) :\n    tm.initCfg x = Cfg.init tm.q₀ x := rfl'),
      ('Cfg.init', 'example {k : ℕ} {S : Type} (q : S) (x : List Bool) :\n    (Cfg.init (k := k) (Symbol := Bool) q x).state = some q := rfl'),
      ('controlAction', 'example {k : ℕ} {S : Type} (m : SignType) (q : Option S) :\n    (FinTM.controlAction (k := k) m q).state = q := rfl'),
      ('tapeAction', 'example {k : ℕ} (i : Fin k) :\n    (tapeAction (Symbol := Bool) i 0 none 0 true).state = some true := rfl'),
      ('bufferedCompTM', 'example (M₁ M₂ : FinTM Bool) : (FinTM.bufferedCompTM M₁ M₂).k = M₁.k + (1 + M₂.k) := rfl'),
      ('embedSilentCfg', 'example {m n : ℕ} {S : Type} {x : List Bool} (ι : Fin m ↪ Fin n) (cap : Fin n)\n    (c : Cfg m Bool S x) :\n    (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] [] c).state = c.state := rfl'),
      ('workTapeSymbols', 'example {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) (i : Fin k) :\n    c.workTapeSymbols i = c.workTapes i (c.workTapePos i) := rfl'),
      ('unaryFin', 'example : unaryFin (2 : Fin 3) = [true, true, false] := by rfl'),
      ('Action.apply by simp', 'example {k : ℕ} {S : Type} {x : List Bool} (a : Action k Bool S) (c : Cfg k Bool S x) :\n    (a.apply c).state = a.state := by simp'),
      ('initCfg by simp', 'example {k : ℕ} {S : Type} (tm : MultiTapeTM k Bool S) (x : List Bool) :\n    (tm.initCfg x).inputPos = 1 := by simp'),
    ]
    out = []
    for i, (n, body) in enumerate(C, 1):
        out += [f'/-- Control {tag}{i}: closes only by unfolding `{n}`. -/', body, '']
    return out
body = L[s:e] if keep else []
if ctrl: body = controls('top-') + body + controls('end-')
L = L[:s] + ['section U2SSeal'] + att + [''] + body + ['end U2SSeal', ''] + L[e:]
open(out, 'w', encoding='utf-8').write('\n'.join(L))
print('wrote %s: seal %s (%d names), erase %s, controls %s, body %s' % (out.split('/')[-1], seal, len(names), erase, ctrl, keep))
