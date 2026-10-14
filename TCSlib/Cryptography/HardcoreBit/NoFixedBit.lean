/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.HardcoreBit.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# No fixed input bit is hard-concentrate

[Gar26, Claim 2.3]: from any function `f` one builds `g(x, y) = f(x_{-y}) ‖ x_y ‖ y`,
which reveals the `y`-th bit of `x` and hides it from `f`. Then no fixed input bit
`x_i` of `g` is a hard-concentrate bit: the predictor that outputs the revealed bit when
`y = i` and a coin flip otherwise is correct with probability exactly
`1/2 + 1/(2 · #positions)`.

The concrete encoding: `x` has `n + 1` bits, the position `y` is an element of
`Fin (n + 1)` (the source writes it with `log n` bits, which needs `n` to be a power of
two), and `f` is applied to the `n` remaining bits (the source applies an `n`-bit function
to the `n - 1` remaining bits). That `g` is one-way when `f` is, left as an exercise in
the source, is not formalized here.

## Main definitions

* `dropPad f`: the function `g(x, y) = f(x_{-y}) ‖ x_y ‖ y`.
* `inputBit i`: the bit `B_i(x, y) = x_i`.
* `fixedBitPredictor i`: the predictor of `x_i` from `g(x, y)`, using one coin bit.

## Main results

* `predProb_fixedBitPredictor`: the predictor is correct with probability exactly
  `1/2 + 1/(2 (n + 1))`. [Gar26, Claim 2.3].
* `predProb_positionBit`: any bit of the position `y` is predicted with certainty.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5, Claim 2.3.
-/

namespace TCSlib.Cryptography.HardcoreBit

open Finset TCSlib.Cryptography

variable {n : ℕ} {β : Type*}

/-- The padded function of [Gar26, Claim 2.3]: on `x ∈ {0,1}^{n+1}` and a position
`y ∈ [n + 1]` it outputs `f(x_{-y}) ‖ x_y ‖ y`, where `x_{-y}` is `x` with the `y`-th bit
removed. Deviation: `y` ranges over `Fin (n + 1)` rather than `log n`-bit strings, and `f`
takes the `n` remaining bits. -/
def dropPad (f : (Fin n → Bool) → β) (z : (Fin (n + 1) → Bool) × Fin (n + 1)) :
    β × Bool × Fin (n + 1) :=
  (f (fun j => z.1 (z.2.succAbove j)), z.1 z.2, z.2)

/-- The fixed input bit `B_i(x, y) = x_i` of [Gar26, Claim 2.3]. -/
def inputBit (i : Fin (n + 1)) (z : (Fin (n + 1) → Bool) × Fin (n + 1)) : Bool := z.1 i

/-- The predictor `A_i` of [Gar26, Claim 2.3]: on `f(x_{-y}) ‖ b ‖ y` it outputs the
revealed bit `b` if `y = i` and its coin `c` otherwise. It makes no call to `f`, uses one
coin bit and one comparison of positions. -/
def fixedBitPredictor (i : Fin (n + 1)) (w : β × Bool × Fin (n + 1)) (c : Bool) : Bool :=
  if w.2.2 = i then w.2.1 else c

/-- A uniform bit equals a fixed bit with probability `1/2`. -/
theorem uprob_bool_eq (b : Bool) : uprob (fun c : Bool => c = b) = 1 / 2 := by
  classical
  rw [uprob_eq_card_filter, filter_eq' univ b]
  simp

/-- A uniform position in `Fin (n + 1)` equals a fixed one with probability `1/(n + 1)`. -/
theorem uprob_fin_eq (i : Fin (n + 1)) :
    uprob (fun y : Fin (n + 1) => y = i) = 1 / (n + 1) := by
  classical
  rw [uprob_eq_card_filter, filter_eq' univ i]
  simp

/-- No fixed input bit of `g(x, y) = f(x_{-y}) ‖ x_y ‖ y` is hard-concentrate: the
predictor `A_i` outputs `x_i` with probability exactly `1/2 + 1/(2(n + 1))` over uniform
`x`, `y` and its coin, for every function `f`. [Gar26, Claim 2.3], whose computation is
`(n-1)/n · 1/2 + 1/n · 1 = 1/2 + 1/(2n)` with `n` positions; here there are `n + 1`.

**Proof sketch.** Condition on `y`: if `y = i` the revealed bit is `x_i` and the predictor
is always right; otherwise it outputs an independent coin, right with probability `1/2`.
Averaging over `y`, which equals `i` with probability `1/(n + 1)`, gives
`1/2 + 1/(2(n + 1))`. -/
theorem predProb_fixedBitPredictor (f : (Fin n → Bool) → β) (i : Fin (n + 1)) :
    predProb (dropPad f) (inputBit i) (fixedBitPredictor i) = 1 / 2 + 1 / (2 * (n + 1)) := by
  classical
  unfold predProb
  rw [uprob_prod]
  -- the section over the coin depends only on whether `y = i`
  have hsec : ∀ z : (Fin (n + 1) → Bool) × Fin (n + 1),
      uprob (fun c : Bool => fixedBitPredictor i (dropPad f z) c = inputBit i z) =
        1 / 2 + (1 / 2) * (if z.2 = i then (1 : ℝ) else 0) := by
    rintro ⟨x, y⟩
    by_cases hy : y = i
    · subst hy
      simp only [fixedBitPredictor, dropPad, inputBit, if_true]
      rw [uprob_true]
      norm_num
    · simp only [fixedBitPredictor, dropPad, inputBit, hy, if_false, mul_zero, add_zero]
      exact uprob_bool_eq _
  simp only [hsec]
  rw [uexp_add, uexp_const, uexp_const_mul, uexp_prod]
  simp only
  have hc : (uexp fun _ : Fin (n + 1) → Bool =>
      uexp fun b : Fin (n + 1) => if b = i then (1 : ℝ) else 0) =
      uexp fun b : Fin (n + 1) => if b = i then (1 : ℝ) else 0 := uexp_const _
  rw [hc, ← uprob_eq_uexp_ite, uprob_fin_eq]
  field_simp

/-- Every bit of the position `y` is predicted with certainty from
`g(x, y) = f(x_{-y}) ‖ x_y ‖ y`, since `y` is part of the output. [Gar26, Claim 2.3], the
remark that the bits `B_i` for `i ∈ [n + 1, n + log n]` are clearly not
hard-concentrate. The predictor ignores its (trivial) coin. -/
theorem predProb_positionBit (f : (Fin n → Bool) → β) (h : Fin (n + 1) → Bool) :
    predProb (dropPad f) (fun z => h z.2) (fun w (_ : Unit) => h w.2.2) = 1 :=
  uprob_eq_one_of_forall fun _ => rfl

end TCSlib.Cryptography.HardcoreBit
