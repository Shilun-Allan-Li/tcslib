/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.Seam

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The step block's seam layout from a captured serialization

The startups of the step-block simulators (the deterministic universal machine's U2-S, H1, and
the nondeterministic interpreter core R of C1) capture a machine's canonical serialization
`serializeK M = pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)` on a scratch tape. The step
block's represented start (`Turing.StepBlock.Rep`) instead wants the bare table on the table tape
and the unary initial state on the summary tape from cell `2`. This module states the one machine
that redistributes the first into the second, so that every startup cites it (the user's ruling of
2026-10-17, C1-R's review, gap G2).

## Main results

* `Turing.exists_seamLayoutTM` — the redistribution's contract (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, the machine encoding.)
-/

namespace Turing

/-- **The seam layout from a captured serialization.** For distinct work tapes `src`, `tbl` and
`sm` there is a machine with an entry state `entry`, a live exit `done` and a constant `C` such
that: started at `entry` with tape `src` holding exactly the word
`s = pairEncode a ((List.replicate q true ++ [false]) ++ v)` from cell `0` (blank elsewhere), its
head anywhere from `0` to `|s|`, and tapes `tbl` and `sm` blank with their heads at `0`, it
reaches `done` within `C·(|s| + 1)` steps, and not before, with
* tape `tbl` holding exactly `v` from cell `0`;
* tape `sm` holding exactly the unary word `List.replicate q true ++ [false]` from cell `2`
  (cells `0` and `1` blank);
* tape `src` blank;
* the heads of the three tapes at `0`, and every other tape, head, the input position and the
  output unchanged; it emits nothing.

At `a = n.bits`, `q = M.q₀` and `v = tableBitsK M.tr`, the start word is `serializeK M`
(`Turing.serializeK_eq`, `Turing.unaryFin_eq`), and the end is the step block's table and summary
tapes for an empty output (`Turing.StepBlock.summaryCells_eq`,
`Turing.StepBlock.outputSummary_nil`). (A row of the construction layer; [AB09, §1.4].)

**Proof sketch.** Phases composed by `Turing.phaseHostTM`, each a catalog row through its
`_run_ofCfg` contract or a small leaf:
- rewind `src` to cell `0` (`Turing.skipBackTM_run_ofCfg`, then one step right);
- skip the doubled region of `pairEncode` up to and over its separator `[false, true]` (a leaf
  reading two cells per round: equal cells continue, `false, true` ends; no row reads pairs);
- move the head of `sm` two cells right, and copy the unary word up to and including its first
  `false` onto `sm` (a leaf: the copy row stops at a blank, not at a `false`);
- copy the rest `v` onto `tbl` (`Turing.copyTM_run_ofCfg`);
- rewind `tbl` and `sm` to cell `0` (`Turing.skipBackTM_run_ofCfg`), and clear `src` from cell `0`
  (`Turing.clearTM_run_ofCfg`, then rewind).
Each phase costs `O(|s| + 1)`. Fill obligations, named: the two leaves, the phase joins, and the
endpoint's frame. -/
theorem exists_seamLayoutTM (k : ℕ) (src tbl sm : Fin k) (hst : src ≠ tbl) (hss : src ≠ sm)
    (hts : tbl ≠ sm) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM k Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ {z : List Bool} (d : Cfg k Bool Q z) (a v : List Bool) (q : ℕ),
        let s := pairEncode a ((List.replicate q true ++ [false]) ++ v)
        d.state = some entry →
        d.workTapes src = FinTM.bufferTape s →
        0 ≤ d.workTapePos src → d.workTapePos src ≤ (s.length : ℤ) →
        d.workTapes tbl = (fun _ => none) → d.workTapePos tbl = 0 →
        d.workTapes sm = (fun _ => none) → d.workTapePos sm = 0 →
        ∃ T ≤ C * (s.length + 1),
          (L.runFrom d T).state = some done ∧
          (L.runFrom d T).inputPos = d.inputPos ∧
          (L.runFrom d T).workTapes =
            Function.update (Function.update (Function.update d.workTapes src (fun _ => none))
              tbl (FinTM.bufferTape v))
              sm (fun p => FinTM.bufferTape (List.replicate q true ++ [false]) (p - 2)) ∧
          (L.runFrom d T).workTapePos =
            Function.update (Function.update (Function.update d.workTapePos src 0) tbl 0) sm 0 ∧
          (∀ u ≤ T, (L.runFrom d u).output = d.output) ∧
          ∀ u < T, (L.runFrom d u).state ≠ some done := by
  sorry

end Turing
