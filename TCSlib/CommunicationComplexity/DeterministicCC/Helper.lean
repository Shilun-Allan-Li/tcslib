/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.BooleanRing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Boolean Helper Definitions for Communication Complexity

Basic vocabulary for Boolean inputs `Fin n → Bool`: the all-zero input, the `{0,1} → {±1}`
encoding of [OD14, §1.1], and flipping a single coordinate.

## Main definitions

- `CommunicationComplexity.BoolInput`, `CommunicationComplexity.zeroInput`: `n`-bit Boolean
  inputs and the all-zero input
- `CommunicationComplexity.boolSign`: the `±1` sign attached to a Boolean value
  (`false` → `1`, `true` → `-1`)
- `CommunicationComplexity.flipAt`: flipping one coordinate of a Boolean input

## Main results

- `CommunicationComplexity.boolSign_xor`, `CommunicationComplexity.boolSign_sum`: `boolSign`
  turns xor (and Boolean sums) into multiplication in `{±1}`
- `CommunicationComplexity.boolSign_mul_boolSign_eq_sub_two_indicator`: the product of two
  signs is `1 - 2·[a ≠ b]`
- `CommunicationComplexity.flipAt_flipAt`, `CommunicationComplexity.flipAt_bijective`:
  flipping a coordinate is an involution, hence a bijection

## References

* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

/-- The type of `n`-bit Boolean inputs. -/
abbrev BoolInput (n : Nat) := Fin n → Bool

/-- The all-zero `n`-bit Boolean input. -/
def zeroInput (n : Nat) : BoolInput n := fun _ => false

/-- A Boolean input is nonzero exactly when some coordinate is `true`. -/
lemma exists_true_of_ne_zeroInput {n : ℕ} {x : BoolInput n} (hx : x ≠ zeroInput n) :
    ∃ i, x i = true := by
  by_contra hx'
  apply hx
  funext i
  by_cases hxi : x i = true
  · exact False.elim <| hx' ⟨i, hxi⟩
  · cases h : x i <;> simp [zeroInput, h] at *

/-- The `±1` sign attached to a Boolean value. We use `1` for `false`
and `-1` for `true`, i.e. the encoding `b ↦ (-1)^b` of [OD14, §1.1]. -/
def boolSign (b : Bool) : ℝ :=
  if b then -1 else 1

/-- The sign of an exclusive or is the product of the signs: `boolSign (a xor b)` equals
`boolSign a * boolSign b`. This is the one-bit case of the character identity
`χ_S · χ_T = χ_{S △ T}` [OD14, §1.3]. -/
@[simp] lemma boolSign_xor (a b : Bool) :
    boolSign (Bool.xor a b) = boolSign a * boolSign b := by
  cases a <;> cases b <;> norm_num [boolSign]

/-- The sign of a Boolean sum factors as the product of the signs of its summands. -/
lemma boolSign_sum {α : Type*} (s : Finset α) (f : α → Bool) :
    boolSign (Finset.sum s f) = Finset.prod s (fun i => boolSign (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [boolSign]
  | insert a s ha hs =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      change boolSign (Bool.xor (f a) (Finset.sum s f)) = _
      rw [boolSign_xor]
      simpa [mul_assoc] using congrArg (fun t => boolSign (f a) * t) hs

/-- Two `boolSign` factors collapse to `1 - 2 * indicator(a ≠ b)`. -/
lemma boolSign_mul_boolSign_eq_sub_two_indicator
    (a b : Bool) :
    boolSign a * boolSign b = (1 : ℝ) - 2 * (if a ≠ b then 1 else 0) := by
  cases a <;> cases b <;> norm_num [boolSign]

/-- Flipping one coordinate of a Boolean input. -/
def flipAt {n : ℕ} (i : Fin n) (x : BoolInput n) : BoolInput n :=
  Function.update x i (!(x i))

/-- Flipping coordinate `i` negates the value at coordinate `i`. -/
@[simp] lemma flipAt_apply_same {n : ℕ} (i : Fin n) (x : BoolInput n) :
    flipAt i x i = !(x i) := by
  simp [flipAt]

/-- Flipping coordinate `i` leaves every other coordinate `j ≠ i` unchanged. -/
@[simp] lemma flipAt_apply_ne {n : ℕ} {i j : Fin n} (hij : j ≠ i) (x : BoolInput n) :
    flipAt i x j = x j := by
  simp [flipAt, hij]

/-- Flipping the same coordinate twice returns the original input. -/
@[simp] lemma flipAt_flipAt {n : ℕ} (i : Fin n) (x : BoolInput n) :
    flipAt i (flipAt i x) = x := by
  ext j
  by_cases hij : j = i
  · subst hij
    simp [flipAt]
  · simp [flipAt, hij]

/-- Flipping a fixed coordinate is a bijection of `n`-bit inputs (it is its own inverse). -/
lemma flipAt_bijective {n : ℕ} (i : Fin n) :
    Function.Bijective (flipAt i : BoolInput n → BoolInput n) := by
  refine Function.bijective_iff_has_inverse.mpr ?_
  exact ⟨flipAt i, flipAt_flipAt i, flipAt_flipAt i⟩

end CommunicationComplexity
