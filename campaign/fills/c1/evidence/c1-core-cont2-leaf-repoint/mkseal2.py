"""Seal test for NDCodeSimulator (C1 R cont2; the leaf re-point: the review's mkseal.py plus Turing.inputRewindTM): wrap the body between `namespace Turing` and the
last `end Turing` in a section that makes the named other-file definitions `local irreducible`
(optionally also erasing the four `@[simp]`-unfoldable definitions from the simp set), with
optional controls at the top and at the end of the section. Each `rfl` control closes only by
unfolding one sealed definition (one per sealed definition), so each must fail sealed and pass
unsealed; the four `simp` controls close only through a `@[simp]` definition's unfolding.
usage: python3 -I mkseal.py <module> <out> <names file> <seal 0|1> <erase 0|1> <controls 0|1> [body 0|1] [simp controls 0|1, default = erase]"""
import sys
src, out, nf = sys.argv[1], sys.argv[2], sys.argv[3]
seal, erase, ctrl = sys.argv[4] == '1', sys.argv[5] == '1', sys.argv[6] == '1'
keep = (sys.argv[7] == '1') if len(sys.argv) > 7 else True
simpctl = (sys.argv[8] == '1') if len(sys.argv) > 8 else erase
toponly = len(sys.argv) > 9 and sys.argv[9] == 'top'
names = [l.strip() for l in open(nf, encoding='utf-8') if l.strip()]
L = open(src, encoding='utf-8').read().split('\n')
assert L.count('namespace Turing') == 1, 'namespace Turing not unique'
s = L.index('namespace Turing') + 1
e = max(i for i, l in enumerate(L) if l == 'end Turing')
SIMPDEFS = ['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg', 'Turing.NDTM.initCfg']
att = (['attribute [local irreducible] ' + n for n in names] if seal else []) + \
      (['attribute [-simp] ' + n for n in SIMPDEFS] if erase else [])
RFL = [
 ('Turing.inputRewindTM', 'example (k : ℕ) : (inputRewindTM k).q₀ = .start := rfl'),
 ('Turing.Action.apply', 'example {k : ℕ} {S : Type} {x : List Bool} (a : Action k Bool S) (c : Cfg k Bool S x) :\n    (a.apply c).state = a.state := rfl'),
 ('Turing.Cfg.init', 'example {k : ℕ} {S : Type} (q : S) (x : List Bool) :\n    (Cfg.init (k := k) (Symbol := Bool) q x).state = some q := rfl'),
 ('Turing.Cfg.inputSymbol', 'example (t : Fin 1 → ℤ → Option Bool) (p : Fin 1 → ℤ) :\n    (⟨none, 0, t, p, []⟩ : Cfg 1 Bool Unit [true]).inputSymbol = none := rfl'),
 ('Turing.Cfg.mapState', "example {k : ℕ} {S S' : Type} {x : List Bool} (f : S → S') (c : Cfg k Bool S x) :\n    (c.mapState f).inputPos = c.inputPos := rfl"),
 ('Turing.Cfg.ofWords', 'example {k : ℕ} {S : Type} {x : List Bool} (q : S) (w : Fin k → List Bool) :\n    (Cfg.ofWords (input := x) q w).inputPos = 1 := rfl'),
 ('Turing.Cfg.workTapeSymbols', 'example {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) (i : Fin k) :\n    c.workTapeSymbols i = c.workTapes i (c.workTapePos i) := rfl'),
 ('Turing.CodeNDTM.toFinNDTM', 'example (M : CodeNDTM) : M.toFinNDTM.k = 2 := rfl'),
 ('Turing.FinTM.ComputesFunInTime', 'example (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ) :\n    M.ComputesFunInTime f T =\n      ∀ input : List Bool, M.ComputesInTime input (f input) (T input.length) := rfl'),
 ('Turing.FinTM.VirtualTag', 'example {n : ℕ} (p : Fin (n + 2)) (b : Bool) :\n    FinTM.VirtualTag p b = ((p.val = 0 → b = false) ∧ (p.val = n + 1 → b = true)) := rfl'),
 ('Turing.FinTM.bufferTape', 'example : FinTM.bufferTape [true] 0 = some true := rfl'),
 ('Turing.FinTM.controlAction', 'example {k : ℕ} {S : Type} (m : SignType) (q : Option S) :\n    (FinTM.controlAction (k := k) m q).state = q := rfl'),
 ('Turing.FinTM.pairExtractTM', 'example : (FinTM.pairExtractTM true false).k = 1 := rfl'),
 ('Turing.MultiTapeTM.initCfg', 'example {k : ℕ} {S : Type} (tm : MultiTapeTM k Bool S) (x : List Bool) :\n    tm.initCfg x = Cfg.init tm.q₀ x := rfl'),
 ('Turing.MultiTapeTM.runFrom', 'example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) :\n    tm.runFrom c 0 = c := rfl'),
 ('Turing.MultiTapeTM.step', 'example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)\n    (p : Fin (x.length + 2)) (t : Fin k → ℤ → Option Bool) (h : Fin k → ℤ) :\n    tm.step (⟨none, p, t, h, []⟩ : Cfg k Bool S x) = ⟨none, p, t, h, []⟩ := rfl'),
 ('Turing.NDTM.initCfg', 'example {k : ℕ} {S : Type} (tm : NDTM k Bool S) (x : List Bool) :\n    tm.initCfg x = Cfg.init tm.q₀ x := rfl'),
 ('Turing.NDTM.replayTM', 'example {k : ℕ} {S : Type} (N : NDTM k Bool S) : N.replayTM.q₀ = N.q₀ := rfl'),
 ('Turing.NDTM.runWith', 'example {k : ℕ} {S : Type} {x : List Bool} (tm : NDTM k Bool S) (c : Cfg k Bool S x) :\n    tm.runWith [] c = c := rfl'),
 ('Turing.NDTM.withChoiceTape', 'example {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) (ct : ℤ → Option Bool)\n    (cp : ℤ) : (NDTM.withChoiceTape c ct cp).inputPos = c.inputPos := rfl'),
 ('Turing.StepBlock.Rep', 'example {k n : ℕ} {x : List Bool}\n    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))\n    (c : Cfg k Bool (Fin (n + 1)) x) (d : Cfg (k + 2) Bool (Σ key, StepBlock.Ph k key) x) :\n    StepBlock.Rep tr c d = (d.inputPos = c.inputPos ∧\n      (∀ i : Fin k, d.workTapes (Fin.castAdd 2 i) = c.workTapes i ∧\n        d.workTapePos (Fin.castAdd 2 i) = c.workTapePos i) ∧\n      d.workTapes (StepBlock.tableTape k) = FinTM.bufferTape (tableBitsK tr) ∧\n      d.workTapes (StepBlock.summaryTape k) =\n        StepBlock.summaryCells (StepBlock.outputSummary c.output) ((c.state.map unaryFin).getD []) ∧\n      d.workTapePos (StepBlock.tableTape k) = 0 ∧ d.workTapePos (StepBlock.summaryTape k) = 0) :=\n  rfl'),
 ('Turing.StepBlock.exit', 'example (k : ℕ) : (StepBlock.exit k true).1 = StepBlock.Key.entry := rfl'),
 ('Turing.StepBlock.hostedLoopTM', 'example (k : ℕ) : StepBlock.hostedLoopTM k = vhostEmitTM (StepBlock.loopTM k) := rfl'),
 ('Turing.StepBlock.outputSummary', 'example : StepBlock.outputSummary [] = none := rfl'),
 ('Turing.StepBlock.summaryCells', 'example (s : Option Bool) (w : List Bool) : StepBlock.summaryCells s w 0 = s := rfl'),
 ('Turing.StepBlock.summaryTape', 'example (k : ℕ) : StepBlock.summaryTape k = Fin.natAdd k (1 : Fin 2) := rfl'),
 ('Turing.StepBlock.tableTape', 'example (k : ℕ) : StepBlock.tableTape k = Fin.natAdd k (0 : Fin 2) := rfl'),
 ('Turing.copyTM', 'example {k : ℕ} (src dst : Fin k) : (copyTM (Symbol := Bool) k src dst).q₀ = .sweep := rfl'),
 ('Turing.counterLoopCfg', 'example {k : ℕ} {S : Type} {x : List Bool} (q : Option (CounterLoopState S))\n    (c : Cfg k Bool S x) (ct : ℤ → Option Bool) (cp : ℤ) :\n    (counterLoopCfg q c ct cp).state = q := rfl'),
 ('Turing.counterValue', 'example : counterValue [] = 0 := rfl'),
 ('Turing.embedSilentCfg', 'example {m n : ℕ} {S : Type} {x : List Bool} (ι : Fin m ↪ Fin n) (cap : Fin n)\n    (c : Cfg m Bool S x) :\n    (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] [] c).state = c.state := rfl'),
 ('Turing.embedSilentRetTM', 'example {m n : ℕ} {S : Type} (ι : Fin m ↪ Fin n) (cap : Fin n) (M : MultiTapeTM m Bool S) :\n    (embedSilentRetTM ι cap M).q₀ = Sum.inl M.q₀ := rfl'),
 ('Turing.embedSilentTM', 'example {m n : ℕ} {S : Type} (ι : Fin m ↪ Fin n) (cap : Fin n) (M : MultiTapeTM m Bool S) :\n    (embedSilentTM ι cap M).q₀ = M.q₀ := rfl'),
 ('Turing.moveInputPos', 'example : moveInputPos (n := 1) (0 : Fin 3) 0 = 0 := rfl'),
 ('Turing.pairDecode', 'example : pairDecode [false, true] = some ([], []) := rfl'),
 ('Turing.pairEncode', 'example : pairEncode [] [true] = [false, true, true] := rfl'),
 ('Turing.phaseHostTM', 'example {k : ℕ} {I : Type} {Ph : I → Type} (M : (i : I) → MultiTapeTM k Bool (Ph i))\n    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) :\n    (phaseHostTM M q0 red).q₀ = q0 := rfl'),
 ('Turing.prefixCanonTM', 'example (F : FinTM Bool) : prefixCanonTM F = FinTM.bufferedCompTM universalPrefixTM F := rfl'),
 ('Turing.rewindTM', 'example {k : ℕ} (i : Fin k) : (rewindTM (Symbol := Bool) k i).q₀ = RewindPhase.start := rfl'),
 ('Turing.seamCompTM', 'example {k : ℕ} {S₁ S₂ : Type} [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁) (e : S₁)\n    (M₂ : MultiTapeTM k Bool S₂) (q : S₂) : (seamCompTM M₁ e M₂ q).q₀ = Sum.inl M₁.q₀ := rfl'),
 ('Turing.seamReleaseTM', 'example {k : ℕ} {S : Type} (M : MultiTapeTM k Bool S) (a : S) :\n    (seamReleaseTM M a).q₀ = Sum.inl () := rfl'),
 ('Turing.serializeK', 'example {k n : ℕ} (M : MultiTapeTM k Bool (Fin (n + 1))) :\n    serializeK M = pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr) := rfl'),
 ('Turing.stateWord', 'example (k : ℕ) (s : List Bool) :\n    stateWord k s = fun i : Fin k => if (i : ℕ) = 0 then s else [] := rfl'),
 ('Turing.tableBitsK', 'example {k n : ℕ}\n    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1))) :\n    tableBitsK tr = (List.finRange (n + 1)).flatMap fun q =>\n      ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>\n        (workReadsK k).flatMap fun w => actionBitsK (tr q inp w) := rfl'),
 ('Turing.unaryFin', 'example : unaryFin (2 : Fin 3) = [true, true, false] := rfl'),
 ('Turing.vhostBank', 'example {m : ℕ} (i : Fin m) : vhostBank i = Fin.natAdd 1 i := rfl'),
 ('Turing.vhostCfg', 'example {m : ℕ} {S : Type} {x y : List Bool} (c : Cfg m Bool S y) (b : Bool)\n    (p : Fin (x.length + 2)) (pre : List Bool) : (vhostCfg c b p pre).inputPos = p := rfl'),
]
SIMP = [
 ('Turing.Action.apply', 'example {k : ℕ} {S : Type} {x : List Bool} (a : Action k Bool S) (c : Cfg k Bool S x) :\n    (a.apply c).output = c.output ++ a.output.toList := by simp'),
 ('Turing.Cfg.init', 'example {k : ℕ} {S : Type} (q : S) (x : List Bool) :\n    (Cfg.init (k := k) (Symbol := Bool) q x).output = [] := by simp'),
 ('Turing.MultiTapeTM.initCfg', 'example {k : ℕ} {S : Type} (tm : MultiTapeTM k Bool S) (x : List Bool) :\n    tm.initCfg x = Cfg.init tm.q₀ x := by simp'),
 ('Turing.NDTM.initCfg', 'example {k : ℕ} {S : Type} (tm : NDTM k Bool S) (x : List Bool) :\n    tm.initCfg x = Cfg.init tm.q₀ x := by simp'),
]
assert (not ctrl) or sorted(n for n, _ in RFL) == sorted(names), 'controls do not cover the seal set exactly'
def controls(tag):
    out = []
    for i, (n, body) in enumerate(RFL, 1):
        out += [f'/-- Control {tag}R{i}: closes only by unfolding `{n}` (rfl). -/', body, '']
    if simpctl:
        for i, (n, body) in enumerate(SIMP, 1):
            out += [f'/-- Control {tag}S{i}: closes only through the `@[simp]` unfolding of `{n}`. -/', body, '']
    return out
body = L[s:e] if keep else []
if ctrl: body = controls('top-') + body + ([] if toponly else controls('end-'))
L = L[:s] + ['section C2Seal'] + att + [''] + body + ['end C2Seal', ''] + L[e:]
open(out, 'w', encoding='utf-8').write('\n'.join(L))
print('wrote %s: seal %s (%d names), erase %s, controls %s (%d rfl%s), body %s' % (out.split('/')[-1], seal, len(names) if seal else 0, erase, ctrl, len(RFL), ' + %d simp' % len(SIMP) if (ctrl and simpctl) else '', keep))
