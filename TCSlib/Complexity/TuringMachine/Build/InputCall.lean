/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CounterLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: modules on the native input (§12.8)

The two native-input modules of the §12.8 rich-alphabet design
(`machine-library-design.md` §12.8a §3): a call of a function-level machine
on the native input at a clean seam (R8.5e), and a seek of the input head to a
position held in binary on a work tape (R8.5b). Both are `Bool` modules; a
rich host runs them lifted along its digit embedding
(`Turing.MultiTapeTM.liftSymbols`), with unchanged time and space.

**Status: statements.** Both rows are existential modules in the
`Turing.FinTM.exists_installCallTM` style, sorried with construction sketches,
pending the §12.8 fill.

## Main results

* `Turing.FinTM.exists_inputCallTM` — compute `f` on the native input from a
  blank seam and install the result on tape `0` (statement).
* `Turing.exists_inputSeekTM` — move the input head to the binary value on a
  counter tape, restoring every work tape (statement).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the read-only input tape, whose
  head a work-tape counter can position; the space-bounded simulations of
  §4.1 locate the input head of a simulated configuration this way.)
-/

namespace Turing.FinTM

/-- **R8.5e, the clean call on the native input** (design §12.8a §3). For any
witness `M` computing `f` within `T`, there is a callable module with entry and
exit states and a positive tape count with the following contract. From the
blank seam `Cfg.ofWords entry` (every tape empty, input head at `1`, empty
output) over the native input `x`, the module reaches, at its first positive
visit to `exit`, exactly the seam with `f x` installed on tape `0`, within
`c·(T |x| + |x| + |f x| + 1)` steps. It is the function-level contract run at a
seam that the next phase of a host can consume.

**Proof sketch.** Seam-compose (`Turing.seamCompTM_run_ofCfg`) the input
copier on tape `0` (`Turing.inputCopyTM_run_ofCfg`, `2|x| + 2` steps, which
from the blank seam yields `Cfg.ofWords` with `x` on tape `0`) with the install
call of `Turing.FinTM.exists_installCallTM` on the argument `x`, whose
coefficient absorbs the copy and the dispatch step. The first-return clause is
`Turing.seamCompTM_firstReturn_ofCfg`, and the positive tape count is the
install call's. -/
theorem exists_inputCallTM (M : FinTM Bool) (f : List Bool → List Bool)
    (T : ℕ → ℕ) (hM : M.ComputesFunInTime f T) :
    ∃ (C : FinTM Bool) (entry exit : C.State) (c : ℕ), 0 < C.k ∧
      ∀ x : List Bool,
        ∃ t ≤ c * (T x.length + x.length + (f x).length + 1),
          0 < t ∧
          (∀ t', 0 < t' → t' < t →
            (C.tm.runFrom (Cfg.ofWords (input := x) entry (fun _ => [])) t').state ≠
              some exit) ∧
          C.tm.runFrom (Cfg.ofWords (input := x) entry (fun _ => [])) t =
            Cfg.ofWords exit (stateWord C.k (f x)) := by
  sorry

end Turing.FinTM

namespace Turing

/-- **R8.5b, the input seek** (design §12.8a §3). There is a two-tape `Bool`
module with entry and exit states with the following contract. Let tape `0`
hold, from its head, a delimited word `w` whose little-endian value `p` is a
valid input position, at most `|x| + 1`, and let tape `1` be blank. From the
entry, with the input head anywhere, the module reaches `exit` with the input
head at `p` within `C·(|w| + pos + p + 1)` steps, where `pos` is the starting
input position, and not earlier. Every work tape, every work head and the
output are restored. A rich host runs it lifted on two dedicated digit tapes.

**Proof sketch.** Copy `w` to the scratch tape (`Turing.copyTM_run_ofCfg`,
`2|w| + 2`). Rewind the input head to the left end marker (`timed_rewind`, at
most `pos + 1` steps). Run `Turing.counterLoopTM` with the scratch copy as the
counter and the one-step round "input head right", `p` rounds
(`Turing.counterLoopTM_run_done`, `p + counterOverhead w (p + 1)`, at most
`5p + 2|w| + 2` by `Turing.counterOverhead_le`). The counter ends all `true`
with its head back; `Turing.clearTM_run_ofCfg` blanks it. The phases join by
R2 seams, whose dispatch steps add a constant. -/
theorem exists_inputSeekTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 2 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} (p : ℕ) (w : List Bool), Nat.ofDigits 2 (w.map Bool.toNat) = p →
        p ≤ x.length + 1 → ∀ d : Cfg 2 Bool S x, d.state = some entry →
        (∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + q) = FinTM.bufferTape w q) →
        (∀ q, d.workTapes 1 q = none) →
        ∃ t ≤ C * (w.length + d.inputPos.val + p + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (R.runFrom d t).state = some exit ∧ ((R.runFrom d t).inputPos : ℕ) = p ∧
          (R.runFrom d t).workTapes = d.workTapes ∧ (R.runFrom d t).workTapePos = d.workTapePos ∧
          (R.runFrom d t).output = d.output := by
  sorry

end Turing
