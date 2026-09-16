/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bidirectional versus unidirectional tapes

[AB09, Claim 1.8]: tapes that are infinite in both directions are simulated by tapes
infinite in one direction only, with constant-factor slowdown.

## Deviations from [AB09]

Our vendored model's tapes are *already* bidirectional (`ℤ`-indexed) — that choice is
what lets initialization dispense with start markers. So the faithful in-model
rendering of Claim 1.8 runs in the only meaningful direction: every machine is
simulated, with constant-factor slowdown and the same number of work tapes, by one
whose work heads **never visit a negative cell** (`Turing.FinTM.NonnegativeHeads`),
i.e. by a machine that uses its tapes unidirectionally. The simulating machine "folds"
each tape at the origin over the doubled alphabet `Γ × Γ`, exactly as in [AB09]'s
proof.

## Main results

* `Turing.FinTM.NonnegativeHeads` — the unidirectional-use predicate.
* `Turing.FinTM.nonnegative_heads` — [AB09, Claim 1.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.8, p. 18.)
-/

namespace Turing.FinTM

/-- A machine uses its work tapes unidirectionally: in every initialized run, no work
head ever visits a negative cell. -/
def NonnegativeHeads {Γ : Type} (M : FinTM Γ) : Prop :=
  ∀ (input : List Γ) (t : ℕ) (i : Fin M.k),
    0 ≤ (M.tm.runFrom (M.tm.initCfg input) t).workTapePos i

/-- **Unidirectional tapes suffice** [AB09, Claim 1.8]: a `Γ`-machine computing `f`
within `T` is simulated, with the same number of work tapes and constant-factor
slowdown, by a machine over an enlarged alphabet whose work heads never visit negative
cells.

**Proof sketch.** Fold each tape at the origin: cell `j ≥ 0` of the simulating tape
holds the pair (simulated cell `j`, simulated cell `-j - 1`) over the alphabet
`Option Γ × Option Γ` (embedded via `e` in the first component with a blank second
component). The simulator's state tracks, per tape, which component the simulated head
is in. Moves translate directly, flipping component when a simulated head crosses the
origin (detected at cell `0`); each simulated step costs a constant number of steps
(a boundary check may cost one extra), giving `c · (T n + 1)` — [AB09] gets `4T`.
Head positions of the simulator are absolute values of simulated positions, hence
nonnegative, and the folding invariant transfers computation and halting. -/
theorem nonnegative_heads {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.NonnegativeHeads ∧ M'.k = M.k ∧
        M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) := by
  sorry

end Turing.FinTM
