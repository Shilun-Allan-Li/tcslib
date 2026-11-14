/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite position averaging for Lamport's reduction

## Main definitions

None.

## Main results

* `sum_favourable_bits`: a differing pair of message bits has one favourable plant bit.
* `one_le_favourable_sum`: distinct messages have at least one favourable position and bit.
* `favourable_expect_ge`: the favourable fraction is at least `1 / (2 |I|)`.
* `noQuery_expect_eq_half`: without a query the favourable fraction is exactly `1 / 2`.
* `exists_expect_sample_le`: a finite uniform average is bounded by a value it averages.
* `expect_favourable_of_success`: pointwise favourable mass bounds its average on successes.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 137.2. The finite arithmetic is generic glue for its reduction.
-/

namespace TCSlib.Cryptography.Authentication.LamportReduction

open Finset TCSlib.Cryptography.Games

/-- For two bits `a` and `b`, the number of bits `c` satisfying `a ≠ c = b` is one
when `a ≠ b`, and zero otherwise. -/
theorem sum_favourable_bits (a b : Bool) :
    (∑ c : Bool, if a ≠ c ∧ b = c then (1 : ℝ) else 0) = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> simp [Fintype.sum_bool]

/-- The number of position-bit pairs with `m i ≠ c = m' i` is the number of positions at
which the messages differ. [PS10, proof of Theorem 137.2]. -/
theorem sum_favourable_pairs {ι : Type} [Fintype ι] (m m' : ι → Bool) :
    (∑ p : ι × Bool, if m p.1 ≠ p.2 ∧ m' p.1 = p.2 then (1 : ℝ) else 0) =
      ∑ i : ι, if m i ≠ m' i then (1 : ℝ) else 0 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => sum_favourable_bits (m i) (m' i)

/-- Distinct messages have at least one jointly favourable position and bit:
`1 ≤ ∑_(i,c) 1[m_i ≠ c = m'_i]`. [PS10, proof of Theorem 137.2].

**Proof sketch.** Extensional inequality supplies a differing coordinate. Its indicator is
one, and all other indicators in the sum are nonnegative. -/
theorem one_le_favourable_sum {ι : Type} [Fintype ι] {m m' : ι → Bool} (h : m ≠ m') :
    1 ≤ ∑ p : ι × Bool, if m p.1 ≠ p.2 ∧ m' p.1 = p.2 then (1 : ℝ) else 0 := by
  classical
  have hex : ∃ i, m i ≠ m' i := by
    by_contra hh
    push_neg at hh
    exact h (funext hh)
  obtain ⟨i, hi⟩ := hex
  rw [sum_favourable_pairs]
  have hle := Finset.single_le_sum
    (s := Finset.univ) (a := i)
    (f := fun j => if m j ≠ m' j then (1 : ℝ) else 0)
    (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
  simpa only [hi, if_true] using hle

/-- For distinct messages on a nonempty finite position type, uniform `(i,c)` is jointly
favourable with probability at least `1 / (2 |I|)`. [PS10, proof of Theorem 137.2]. -/
theorem favourable_expect_ge {ι : Type} [Fintype ι] [Nonempty ι]
    {m m' : ι → Bool} (h : m ≠ m') :
    1 / (2 * (Fintype.card ι : ℝ)) ≤
      ProbComp.expect (ProbComp.sample (ι × Bool))
        (fun p => if m p.1 ≠ p.2 ∧ m' p.1 = p.2 then (1 : ℝ) else 0) := by
  rw [ProbComp.expect_sample]
  simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  have hcount := one_le_favourable_sum h
  have hden : 0 ≤ ((Fintype.card ι : ℝ) * 2)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcount hden
  simpa only [mul_one, one_div, mul_comm 2 (Fintype.card ι : ℝ)] using hmul

/-- When there was no signing query, a uniform position and bit agrees with the forged
message bit with probability exactly `1 / 2`. [PS10, proof of Theorem 137.2]. -/
theorem noQuery_expect_eq_half {ι : Type} [Fintype ι] [Nonempty ι] (m' : ι → Bool) :
    ProbComp.expect (ProbComp.sample (ι × Bool))
        (fun p => if m' p.1 = p.2 then (1 : ℝ) else 0) = 1 / 2 := by
  have hbit (b : Bool) : (∑ c : Bool, if b = c then (1 : ℝ) else 0) = 1 := by
    cases b <;> simp [Fintype.sum_bool]
  rw [ProbComp.expect_sample, Fintype.sum_prod_type]
  simp only [hbit, sum_const, card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  field_simp

/-- A uniform finite average has a position whose value is at least the average.

**Proof sketch.** A maximum exists on the nonempty finite type. Every term of the sum is at
most that maximum, so the uniform average is at most it. -/
theorem exists_expect_sample_le {ι : Type} [Fintype ι] [Nonempty ι] (g : ι → ℝ) :
    ∃ i, ProbComp.expect (ProbComp.sample ι) g ≤ g i := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc
    ProbComp.expect (ProbComp.sample ι) g ≤
        ProbComp.expect (ProbComp.sample ι) (fun _ => g i) :=
      ProbComp.expect_mono _ (fun j => hi j (Finset.mem_univ j))
    _ = g i := ProbComp.expect_const _ _

/-- If nonnegative favourable mass is at least `b` on every successful output, its average
is at least `b` times the success probability. This is the finite averaging step in
[PS10, proof of Theorem 137.2]. -/
theorem expect_favourable_of_success {α : Type} (c : ProbComp α) (P : α → Prop)
    (q : α → ℝ) (b : ℝ) (hq : ∀ a, 0 ≤ q a) (hP : ∀ a, P a → b ≤ q a) :
    b * ProbComp.prob c P ≤ ProbComp.expect c q := by
  classical
  rw [ProbComp.prob_eq_expect, ← ProbComp.expect_const_mul]
  apply ProbComp.expect_mono
  intro a
  by_cases ha : P a
  · simpa only [ha, if_true, mul_one] using hP a ha
  · simpa only [ha, if_false, mul_zero] using hq a

end TCSlib.Cryptography.Authentication.LamportReduction
