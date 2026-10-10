/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import Mathlib.Analysis.MeanInequalities

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite weighted norm duality

## Main definitions

No new definitions are introduced.

## Main results

* `FiniteNorms.weighted_holder`: Hölder inequality for finite nonnegative weights.
* `FiniteNorms.selfAdjoint_contraction`: same-exponent contraction transfers
  between conjugate norms for self-adjoint operators.

A private signed-power calculation supplies the sharp dual witness.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Proposition 9.19 (proof).
-/

namespace BooleanAnalysis.Hypercontractivity.FiniteNorms

/-- For every real exponent `q > 1` and real number `z`, the signed witness
`g = z * |z| ^ (q - 2)` satisfies `z * g = |z| ^ q` and
`|g| ^ (q / (q - 1)) = |z| ^ q`, including when `z` is zero or negative.
This scalar calculation isolates the Hölder equality witness in
[OD14, Prop. 9.19 (proof)].

**Proof sketch.** Treat zero separately. Otherwise the absolute value is
positive. Rewrite the squared factor as an absolute square and combine real
exponents to obtain the pairing identity. The absolute value of the witness
is the `(q - 1)`st power of the absolute value of `z`; multiplying by the
conjugate exponent gives the second identity. -/
private theorem signed_power_dual (q : ℝ) (hq : 1 < q) (z : ℝ) :
    let g : ℝ := z * |z| ^ (q - 2)
    z * g = |z| ^ q ∧ |g| ^ (q / (q - 1)) = |z| ^ q :=
  (by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  dsimp only
  by_cases hz : z = 0
  · subst z
    simp [Real.zero_rpow hq0, Real.zero_rpow (div_ne_zero hq0 hq1)]
  · have hzpos : 0 < |z| := abs_pos.mpr hz
    constructor
    · calc
        z * (z * |z| ^ (q - 2)) = |z| ^ (2 : ℝ) * |z| ^ (q - 2) := by
          rw [Real.rpow_two, sq_abs, pow_two]
          ring
        _ = |z| ^ (2 + (q - 2)) := (Real.rpow_add hzpos 2 (q - 2)).symm
        _ = |z| ^ q := by congr 1; ring
    · have habs : |z * |z| ^ (q - 2)| = |z| ^ (q - 1) := by
        calc
          |z * |z| ^ (q - 2)| = |z| ^ (1 : ℝ) * |z| ^ (q - 2) := by
            rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg z) _),
              Real.rpow_one]
          _ = |z| ^ (1 + (q - 2)) := (Real.rpow_add hzpos 1 (q - 2)).symm
          _ = |z| ^ (q - 1) := by congr 1; ring
      rw [habs, ← Real.rpow_mul (abs_nonneg z)]
      congr 1
      rw [← mul_div_assoc, mul_div_cancel_left₀ q hq1]
)

open scoped BigOperators

/-- For conjugate real exponents greater than one, the weighted pairing of two
real functions on a finite set is bounded by the product of their weighted
norms. All weights are nonnegative; zero weights and arbitrary total weight
are permitted. This finite weighted formulation supplies the Hölder step in
[OD14, Prop. 9.19 (proof)].

**Proof sketch.** Bound each signed product by its absolute value. Split each
weight into its reciprocal-exponent powers and apply the finite Hölder
inequality. Conjugacy makes the two weight powers multiply back to the
original weight, while raising each factor to its norm exponent recovers
the corresponding weighted moment. -/
theorem weighted_holder {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {p q : ℝ} (hpq : Real.HolderConjugate p q) (f g : ι → ℝ) :
    (∑ i, w i * f i * g i) ≤
      (∑ i, w i * |f i| ^ p) ^ (1 / p) *
        (∑ i, w i * |g i| ^ q) ^ (1 / q) :=
  (by
  classical
  have hinv : 1 / p + 1 / q = 1 := by
    simpa only [one_div] using hpq.inv_add_inv_eq_one
  have hweight (i : ι) : w i ^ (1 / p) * w i ^ (1 / q) = w i := by
    rw [← Real.rpow_add' (hw i) (show 1 / p + 1 / q ≠ 0 by rw [hinv]; norm_num),
      hinv, Real.rpow_one]
  have hpow (r : ℝ) (hr : r ≠ 0) (i : ι) (a : ℝ) :
      (w i ^ (1 / r) * |a|) ^ r = w i * |a| ^ r := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (abs_nonneg a),
      ← Real.rpow_mul (hw i), one_div_mul_cancel hr, Real.rpow_one]
  calc
    (∑ i, w i * f i * g i) ≤ ∑ i, w i * |f i| * |g i| := by
      apply Finset.sum_le_sum
      intro i _
      calc
        w i * f i * g i = w i * (f i * g i) := by ring
        _ ≤ w i * |f i * g i| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (hw i)
        _ = w i * |f i| * |g i| := by rw [abs_mul]; ring
    _ = ∑ i, (w i ^ (1 / p) * |f i|) * (w i ^ (1 / q) * |g i|) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        w i * |f i| * |g i| =
            (w i ^ (1 / p) * w i ^ (1 / q)) * |f i| * |g i| := by
          rw [hweight]
        _ = (w i ^ (1 / p) * |f i|) * (w i ^ (1 / q) * |g i|) := by ring
    _ ≤ (∑ i, (w i ^ (1 / p) * |f i|) ^ p) ^ (1 / p) *
        (∑ i, (w i ^ (1 / q) * |g i|) ^ q) ^ (1 / q) :=
      Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset ι) hpq
        (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (abs_nonneg _))
        (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (abs_nonneg _))
    _ = (∑ i, w i * |f i| ^ p) ^ (1 / p) *
        (∑ i, w i * |g i| ^ q) ^ (1 / q) := by
      simp_rw [hpow p hpq.ne_zero, hpow q hpq.symm.ne_zero]
)

/-- For an exponent `q > 1`, a self-adjoint operator on a finite weighted
real function space is contractive in the weighted `q` norm whenever it is
contractive in the conjugate norm. Weights may vanish and need not sum to one.
This is the finite weighted form of the operator duality argument in
[OD14, Prop. 9.19 (proof)], specialized to equal input and output exponents.

**Proof sketch.** Pair the transformed function with its signed power
witness. The pairing and the witness's conjugate moment both equal the
transformed function's `q`th moment. Move the operator across the pairing,
then apply weighted Hölder and the assumed conjugate contraction. If that
moment is positive, cancel its conjugate root; if it is zero, the desired
bound follows from nonnegativity. -/
theorem selfAdjoint_contraction {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (T : (ι → ℝ) → ι → ℝ)
    (hself : ∀ f g : ι → ℝ,
      (∑ i, w i * T f i * g i) = ∑ i, w i * f i * T g i)
    (q : ℝ) (hq : 1 < q)
    (hcontract : ∀ g : ι → ℝ,
      (∑ i, w i * |T g i| ^ (q / (q - 1))) ^ (1 / (q / (q - 1))) ≤
        (∑ i, w i * |g i| ^ (q / (q - 1))) ^ (1 / (q / (q - 1)))) :
    ∀ f : ι → ℝ,
      (∑ i, w i * |T f i| ^ q) ^ (1 / q) ≤
        (∑ i, w i * |f i| ^ q) ^ (1 / q) :=
  (by
  classical
  intro f
  let p : ℝ := q / (q - 1)
  let g : ι → ℝ := fun i => T f i * |T f i| ^ (q - 2)
  let M : ℝ := ∑ i, w i * |T f i| ^ q
  let N : ℝ := (∑ i, w i * |f i| ^ q) ^ (1 / q)
  have hconj : Real.HolderConjugate q p :=
    (Real.holderConjugate_iff_eq_conjExponent hq).2 rfl
  have hnonneg (r : ℝ) (h : ι → ℝ) : 0 ≤ ∑ i, w i * |h i| ^ r :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _)
  have hpair : (∑ i, w i * T f i * g i) = M := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc]
    congr 1
    exact (signed_power_dual q hq (T f i)).1
  have hmoment : (∑ i, w i * |g i| ^ p) = M := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (signed_power_dual q hq (T f i)).2
  have hbound : M ≤ N * M ^ (1 / p) := by
    calc
      M = ∑ i, w i * f i * T g i := by rw [← hpair, hself f g]
      _ ≤ N * (∑ i, w i * |T g i| ^ p) ^ (1 / p) :=
        weighted_holder w hw hconj f (T g)
      _ ≤ N * (∑ i, w i * |g i| ^ p) ^ (1 / p) :=
        mul_le_mul_of_nonneg_left (hcontract g)
          (Real.rpow_nonneg (hnonneg q f) _)
      _ = N * M ^ (1 / p) := by rw [hmoment]
  change M ^ (1 / q) ≤ N
  by_cases hMzero : M = 0
  · rw [hMzero, Real.zero_rpow (one_div_ne_zero (by linarith : q ≠ 0))]
    exact Real.rpow_nonneg (hnonneg q f) _
  · have hMpos : 0 < M :=
      lt_of_le_of_ne (hnonneg q (T f)) (Ne.symm hMzero)
    apply le_of_mul_le_mul_right
      (a := M ^ (1 / p)) ?_ (Real.rpow_pos_of_pos hMpos _)
    calc
      M ^ (1 / q) * M ^ (1 / p) = M := by
        rw [← Real.rpow_add hMpos,
          show 1 / q + 1 / p = 1 by
            simpa only [one_div] using hconj.inv_add_inv_eq_one,
          Real.rpow_one]
      _ ≤ N * M ^ (1 / p) := hbound
)

end BooleanAnalysis.Hypercontractivity.FiniteNorms
