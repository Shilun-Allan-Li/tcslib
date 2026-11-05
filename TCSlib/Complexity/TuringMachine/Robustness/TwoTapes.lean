/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to two work tapes

[HS66], as used in [AB09, §1.7] for the efficient universal machine: `k` work tapes are simulated
by two work tapes with a slowdown of `O(T log T)`. Run for run, every binary machine has a
binary two-work-tape equivalent that reproduces each halting run of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and whose completed outputs are outputs of the source.

## Deviations from [AB09] and [HS66]

* The slowdown is stated per run, with an existential constant, and padded with `+ 1` in both
  factors so that it covers the empty run (`t = 0`).
* The statement includes the converse (every completed output of the simulator is an output of
  the source), which the universal machine's correctness needs.
* The statement holds for every number of work tapes, zero and one included.

## Main definitions

No new definitions: the reduction is an existential contract.

## Main results

* `Turing.FinTM.two_work_tapes_run` — two work tapes suffice, with logarithmic overhead, run by
  run and with the converse [HS66].
* `Turing.FinTM.two_work_tapes_binary` — the same at the level of computed functions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.7, the proof of Theorem 1.9.)
* [HS66] F. C. Hennie, R. E. Stearns, *Two-tape simulation of multitape Turing machines*,
  J. ACM 13(4), 1966, 533–546.
-/

namespace Turing.FinTM

/-- **Two work tapes suffice, run by run** [HS66]: every binary machine `M` has a binary
equivalent `M'` with two work tapes that reproduces each halting run of `M` of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of `M'` is an output of `M` on
the same input.

**Proof sketch.** (The Hennie–Stearns simulation.) The first work tape of `M'` holds all `k` of
`M`'s work tapes as tracks, folded around a fixed origin cell into zones of doubling sizes
`2^i`, so that every simulated head stays at the origin and a tape movement shifts contents
between neighbouring zones. Each zone is kept half full. A shift that empties or fills a zone `i`
rebalances zones `0, …, i` using the second work tape as scratch, in `O(2^i)` steps, and a zone `i`
is rebalanced at most once every `2^(i-1)` simulated steps. Summing over the `log₂ t + 1` zones a
run of `t` steps reaches gives `O(t log t)` steps in all. The converse holds because `M'` writes
an output symbol exactly when `M` does, in the same order, and halts only when `M` halts. With
no work tapes, `M` is run directly beside two idle tapes. -/
theorem two_work_tapes_run (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  sorry

/-- **Two work tapes suffice** for computing a function: if a binary machine computes `f` within
time `T`, then a binary machine with two work tapes computes `f` within
`c · (T n + 1)(log₂(T n + 1) + 1)` for some constant `c` [HS66].

**Proof sketch.** Apply `Turing.FinTM.two_work_tapes_run` to `M` and use its forward direction at
each input `x`, with the run of `T |x|` steps that computes `f x`. -/
theorem two_work_tapes_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      M'.ComputesFunInTime f fun n => c * ((T n + 1) * (Nat.log 2 (T n + 1) + 1)) := by
  obtain ⟨M', c, hk, h, -⟩ := two_work_tapes_run M
  exact ⟨M', c, hk, fun x => h x (f x) _ (hM x)⟩

end Turing.FinTM
