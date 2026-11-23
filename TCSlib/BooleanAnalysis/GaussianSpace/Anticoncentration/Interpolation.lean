/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Quantitative polynomial interpolation

Absolute-value estimates for Lagrange interpolation provide preparation for
the univariate Remez stage of polynomial anticoncentration.

## Main definitions

The existing polynomial evaluation and Lagrange interpolation are reused.

## Main results

* `abs_eval_le_of_separated_nodes`: control polynomial values using separated
  nodes, retaining the factorial denominator in the interpolation constant.
* `abs_eval_le_lagrange_sum`: bound a polynomial value by its values at
  distinct interpolation nodes and the absolute Lagrange weights.

## References

* [CW01] A. Carbery and J. Wright, Distributional and Lq norm inequalities for
  polynomials over convex bodies in Rn, Mathematical Research Letters 8 (2001),
  233–248, §4, the univariate Remez argument.
-/

open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- A polynomial value is bounded by the sum of its absolute nodal values
times the absolute Lagrange weights. This is a technical preparation for
the univariate Remez argument of [CW01, §4].

**Proof sketch.** Express the polynomial by Mathlib's Lagrange interpolation
formula and evaluate at `x`. Apply the triangle inequality to the finite sum,
then distribute absolute values through each product and quotient. -/
lemma abs_eval_le_lagrange_sum {ι : Type*} [DecidableEq ι]
    (p : Polynomial ℝ) (s : Finset ι) (v : ι → ℝ)
    (hv : Set.InjOn v s) (hp : p.degree < s.card) (x : ℝ) :
    |p.eval x| ≤ ∑ i ∈ s,
      |p.eval (v i)| * ∏ j ∈ s.erase i, (|x - v j| / |v i - v j|) := (by
  have hbasis (i : ι) : (Lagrange.basis s v i).eval x =
      ∏ j ∈ s.erase i, (x - v j) / (v i - v j) := by
    change (∏ j ∈ s.erase i,
      Polynomial.C ((v i - v j)⁻¹) * (Polynomial.X - Polynomial.C (v j))).eval x = _
    simp only [Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X, div_eq_mul_inv, mul_comm]
  have heval := congrArg (Polynomial.eval x) (Lagrange.eq_interpolate hv hp)
  rw [Lagrange.interpolate_apply, Polynomial.eval_finset_sum] at heval
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at heval
  calc
    |p.eval x| = |∑ i ∈ s, p.eval (v i) * (Lagrange.basis s v i).eval x| :=
      congrArg abs heval
    _ ≤ ∑ i ∈ s, |p.eval (v i) * (Lagrange.basis s v i).eval x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, hbasis, Finset.abs_prod]
      simp only [abs_div]
)


/-- The product of the distances from `i` to the other integers in
`{0, …, d}` is `i! * (d-i)!`.

**Proof sketch.** Induct on `d`. At the new right endpoint, the product is
the descending factorial. At an existing index, separate the new factor
`d+1-i` and apply the induction hypothesis and the factorial recurrence. -/
lemma prod_abs_nat_sub_eq_factorials (d i : ℕ) (hi : i ≤ d) :
    (∏ j ∈ (Finset.range (d + 1)).erase i, |(i : ℝ) - (j : ℝ)|) =
      (i.factorial : ℝ) * ((d - i).factorial : ℝ) := (by
  induction d generalizing i with
  | zero =>
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
    subst i
    simp
  | succ d ih =>
    rcases eq_or_lt_of_le hi with rfl | hi'
    · rw [Finset.range_add_one, Finset.erase_insert (by simp)]
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      calc
        (∏ j ∈ Finset.range (d + 1), |((d + 1 : ℕ) : ℝ) - (j : ℝ)|) =
            ∏ j ∈ Finset.range (d + 1), (((d + 1 : ℕ) : ℝ) - (j : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j hj
          apply abs_of_nonneg
          apply sub_nonneg.mpr
          exact_mod_cast (Finset.mem_range.mp hj).le
        _ = _ := by
          rw [Finset.prod_range_natCast_sub, ← Nat.descFactorial_eq_prod_range,
            Nat.descFactorial_self]
    · have hid : i ≤ d := Nat.le_of_lt_succ hi'
      rw [Finset.range_add_one, Finset.erase_insert_of_ne (by omega : d + 1 ≠ i),
        Finset.prod_insert (by simp), ih i hid]
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hi'.le))]
      rw [show d + 1 - i = d - i + 1 by omega, Nat.factorial_succ]
      push_cast
      rw [Nat.cast_sub hid]
      ring
)


/-- The reciprocal factorial products over `0, …, d` sum to `2^d / d!`.

**Proof sketch.** Rewrite each summand as `choose d i / d!`, factor out the
common denominator, and apply the binomial coefficient sum identity. -/
lemma sum_inv_factorial_mul_factorial (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1),
      1 / ((i.factorial : ℝ) * ((d - i).factorial : ℝ))) =
      (2 : ℝ) ^ d / (d.factorial : ℝ) := (by
  calc
    _ = (∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ)) / (d.factorial : ℝ) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.cast_choose ℝ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
      field_simp
    _ = _ := by
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
)


/-- Absolute separation of the nodes bounds each Lagrange denominator below
by `δ^d * i! * (d-i)!`.

**Proof sketch.** Compare each distance with `δ` times the corresponding
integer distance. Factor `δ` out of the product over the `d` other nodes,
then apply the integer-distance factorial identity. -/
lemma lagrange_denominator_lower_bound (d : ℕ) (v : ℕ → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsep : ∀ i ≤ d, ∀ j ≤ d,
      δ * |(i : ℝ) - (j : ℝ)| ≤ |v i - v j|)
    (i : ℕ) (hi : i ≤ d) :
    δ ^ d * (i.factorial : ℝ) * ((d - i).factorial : ℝ) ≤
      ∏ j ∈ (Finset.range (d + 1)).erase i, |v i - v j| := (by
  have hcard : ((Finset.range (d + 1)).erase i).card = d := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
    omega
  calc
    _ = ∏ j ∈ (Finset.range (d + 1)).erase i, δ * |(i : ℝ) - (j : ℝ)| := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hcard,
        prod_abs_nat_sub_eq_factorials d i hi]
      ring
    _ ≤ _ := Finset.prod_le_prod
      (fun _ _ => mul_nonneg hδ (abs_nonneg _))
      (fun j hj => hsep i hi j (Nat.le_of_lt_succ
        (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))))
)


/-- Polynomial values at separated nodes control its value at any point
within distance `R` of those nodes. This is the quantitative interpolation
step preparing the Remez argument of [CW01, §4].

**Proof sketch.** Use the absolute Lagrange interpolation estimate. Bound each
numerator product by `R^d` and each denominator below by
`δ^d * i! * (d-i)!`. Sum the reciprocal factorial products to obtain
`2^d / d!`. -/
lemma abs_eval_le_of_separated_nodes (p : Polynomial ℝ) (d : ℕ)
    (hp : p.natDegree ≤ d) (v : ℕ → ℝ) {δ R a : ℝ}
    (hδ : 0 < δ) (hR : 0 ≤ R) (ha : 0 ≤ a)
    (hsep : ∀ i ≤ d, ∀ j ≤ d,
      δ * |(i : ℝ) - (j : ℝ)| ≤ |v i - v j|)
    (x : ℝ) (hdist : ∀ i ≤ d, |x - v i| ≤ R)
    (hvalue : ∀ i ≤ d, |p.eval (v i)| ≤ a) :
    |p.eval x| ≤ a / (d.factorial : ℝ) * (2 * R / δ) ^ d := (by
  have hv : Set.InjOn v (Finset.range (d + 1)) := by
    intro i hi j hj hij
    have hs := hsep i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    rw [hij, sub_self, abs_zero] at hs
    have hz : |(i : ℝ) - (j : ℝ)| = 0 := by nlinarith [abs_nonneg ((i : ℝ) - j)]
    exact_mod_cast sub_eq_zero.mp (abs_eq_zero.mp hz)
  have hweight (i : ℕ) (hi : i ∈ Finset.range (d + 1)) :
      (∏ j ∈ (Finset.range (d + 1)).erase i, |x - v j| / |v i - v j|) ≤
        R ^ d / (δ ^ d * (i.factorial : ℝ) * ((d - i).factorial : ℝ)) := by
    have hcard : ((Finset.range (d + 1)).erase i).card = d := by
      rw [Finset.card_erase_of_mem hi, Finset.card_range]
      omega
    rw [Finset.prod_div_distrib]
    calc
      _ ≤ R ^ d / (∏ j ∈ (Finset.range (d + 1)).erase i, |v i - v j|) :=
        div_le_div_of_nonneg_right
          (by
            calc
              _ ≤ ∏ _j ∈ (Finset.range (d + 1)).erase i, R :=
                Finset.prod_le_prod (fun _ _ => abs_nonneg _)
                  (fun j hj => hdist j (Nat.le_of_lt_succ
                    (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))))
              _ = _ := by rw [Finset.prod_const, hcard])
          (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (lagrange_denominator_lower_bound d v hδ.le hsep i
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  calc
    |p.eval x| ≤ ∑ i ∈ Finset.range (d + 1),
        |p.eval (v i)| * ∏ j ∈ (Finset.range (d + 1)).erase i,
          (|x - v j| / |v i - v j|) := by
      apply abs_eval_le_lagrange_sum p _ v hv
      rw [Finset.card_range]
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)
    _ ≤ ∑ i ∈ Finset.range (d + 1),
        (a * R ^ d / δ ^ d) * (1 / ((i.factorial : ℝ) * ((d - i).factorial : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ a * (R ^ d / (δ ^ d * (i.factorial : ℝ) * ((d - i).factorial : ℝ))) :=
          mul_le_mul (hvalue i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
            (hweight i hi) (by positivity) ha
        _ = _ := by simp only [div_eq_mul_inv, mul_inv]; ring
    _ = (a * R ^ d / δ ^ d) * ((2 : ℝ) ^ d / (d.factorial : ℝ)) := by
      rw [← Finset.mul_sum, sum_inv_factorial_mul_factorial]
    _ = _ := by
      rw [div_pow, mul_pow]
      ring
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
