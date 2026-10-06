/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Unary work tapes

A work tape (`ℤ → Option Bool`, as in `Turing.Cfg`) holding a natural number `m` in unary:
cells `0, …, m - 1` hold `1` and every other cell is blank. Machines that keep counters on
their work tapes in unary — the Tseitin emitter of
`TCSlib.Complexity.CircuitComplexity.CircuitSatReductionMachineTapes` and the counter
programs of `TCSlib.Complexity.TuringMachine.CounterProg` — increment a counter by writing
`1` on its first blank cell and decrement it by erasing its last cell.

## Main definitions

* `Turing.UnaryTape.ones` — the unary tape of `m`.
* `Turing.UnaryTape.wrT` — the effect of an optional write at a head position.

## Main results

* `Turing.UnaryTape.update_ones_succ`, `Turing.UnaryTape.update_ones_pred` — increment and
  decrement.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the multi-tape machine.)
-/

namespace Turing

namespace UnaryTape

/-- The unary tape of a counter with value `m`: cells `0, …, m - 1` hold `1`. -/
def ones (m : ℕ) : ℤ → Option Bool := fun c => if 0 ≤ c ∧ c < m then some true else none

/-- A unary tape holds `1` on the cells `0, …, m - 1`. -/
theorem ones_lt {m : ℕ} {c : ℤ} (h0 : 0 ≤ c) (h : c < m) : ones m c = some true := by
  simp [ones, h0, h]

/-- A unary tape is blank from cell `m` on. -/
theorem ones_ge {m : ℕ} {c : ℤ} (h : (m : ℤ) ≤ c) : ones m c = none := by
  simp only [ones]; rw [if_neg]; omega

/-- A unary tape is blank left of cell `0`. -/
theorem ones_neg {m : ℕ} {c : ℤ} (h : c < 0) : ones m c = none := by
  simp only [ones]; rw [if_neg]; omega

/-- The unary tape of `0` is blank. -/
theorem ones_zero : ones 0 = fun _ => none := by
  funext c; simp only [ones]; rw [if_neg]; omega

/-- Writing `1` on the first blank cell of the unary tape of `m` gives that of `m + 1`. -/
theorem update_ones_succ (m : ℕ) :
    Function.update (ones m) (m : ℤ) (some true) = ones (m + 1) := by
  funext c
  simp only [Function.update_apply, ones]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Erasing the last cell of the unary tape of `j + 1` gives that of `j`. -/
theorem update_ones_pred (j : ℕ) :
    Function.update (ones (j + 1)) (j : ℤ) none = ones j := by
  funext c
  simp only [Function.update_apply, ones]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Writing at a head position: no write leaves the tape unchanged, a write `some s` sets
the cell `pos` to `s`. -/
def wrT (tape : ℤ → Option Bool) (pos : ℤ) : Option (Option Bool) → ℤ → Option Bool
  | none => tape
  | some s => Function.update tape pos s

end UnaryTape

end Turing
