/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Products.General
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Comparison
import TCSlib.BooleanAnalysis.Hypercontractivity.Concentration
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.General

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Low-degree applications on finite products

## Main definitions

No new definitions are introduced. The norm-comparison constant
`productNormComparisonConstant` is defined in `Parameters`.

## Main results

* `product_lowDegree_norm`: the higher-norm bound for bounded-degree functions.
* `product_lowDegree_l1_l2`: the sharp first-to-second norm comparison.
* `productNormComparisonConstant_le`: an explicit upper bound for the comparison constant.
* `product_oneSided_anticoncentration`: the one-sided probability lower bound.
* `product_lowDegree_concentration`: the optimized bounded-degree tail estimate.
* `ProductAux.noise_norm_two_le`: second-norm contraction for noise rates in `[0, 1]`.

All statements apply to heterogeneous finite coordinate laws. Homogeneous products
are obtained by choosing the same probability law at every coordinate.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §8.3, Theorem 8.35, Theorem 9.21,
  and §10.3, Theorems 10.21–10.24.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

universe u


/-- Noise at a rate between zero and one does not increase the second norm of a
finite-product function. [OD14, §8.3; Thm. 8.35]
The estimate also holds for heterogeneous finite coordinate laws.

**Proof sketch.** Parseval expresses the squared norm as a sum of nonnegative
component second moments. Noise multiplies each moment by the square of a
power of its rate, and each multiplier is at most one. Take square roots. -/
private theorem product_noise_norm_two_le {n : ℕ} (P : FiniteProduct.{u} n)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (f : P.Point → ℝ) :
    P.norm 2 (P.noise c f) ≤ P.norm 2 f := (by
  classical
  unfold FiniteProduct.norm
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_sqrt
  rw [P.parseval (P.noise c f), P.parseval f]
  apply Finset.sum_le_sum
  intro S _
  simp_rw [RandomizationAux.component_noise, mul_pow, P.expect_const_mul]
  calc
    _ ≤ 1 * P.expect (fun x => P.component S f x ^ 2) := by
      apply mul_le_mul_of_nonneg_right
        (pow_le_one₀ (pow_nonneg hc S.card) (pow_le_one₀ hc hc1))
      unfold FiniteProduct.expect
      apply Finset.sum_nonneg
      intro x _
      apply mul_nonneg _ (sq_nonneg _)
      unfold FiniteProduct.mass
      exact Finset.prod_nonneg fun j _ => (P.weight_pos j (x j)).le
    _ = _ := one_mul _
)

/-- Noise at a real scaling `c ≥ 1` increases the second norm of a degree-`k` product
function by at most `c ^ k`. [OD14, Thm. 10.21, proof via Thm. 9.21]
The spectral formulation permits rates above one and heterogeneous coordinate laws.

**Proof sketch.** Parseval expresses the squared noisy norm as the sum of component
second moments multiplied by `c ^ (2 * |S|)`. Components above degree `k` vanish,
and every remaining multiplier is at most `c ^ (2 * k)`. Take square roots. -/
private theorem product_lowDegree_noise_norm_two {n k : ℕ} (P : FiniteProduct.{u} n)
    (c : ℝ) (hc : 1 ≤ c) (f : P.Point → ℝ) (hdeg : P.HasDegreeLE k f) :
    P.norm 2 (P.noise c f) ≤ c ^ k * P.norm 2 f := (by
  classical
  unfold FiniteProduct.norm
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow]
  calc
    _ ≤ Real.sqrt ((c ^ k) ^ 2 * P.expect (fun x => f x ^ 2)) := by
      apply Real.sqrt_le_sqrt
      rw [P.parseval (P.noise c f), P.parseval f, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro S _
      simp_rw [RandomizationAux.component_noise, mul_pow, P.expect_const_mul]
      by_cases hS : S.card ≤ k
      · apply mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (pow_nonneg (zero_le_one.trans hc) S.card)
            (pow_le_pow_right₀ hc hS) 2)
        unfold FiniteProduct.expect
        apply Finset.sum_nonneg
        intro x _
        apply mul_nonneg _ (sq_nonneg _)
        unfold FiniteProduct.mass
        exact Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le
      · simp [hdeg S (Nat.lt_of_not_ge hS), FiniteProduct.expect]
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (pow_nonneg (zero_le_one.trans hc) k)]
)

/-- A degree-`k` product function has `q`-norm at most
`(√(q-1) lam^(1/q-1/2))^k` times its `2`-norm. [OD14, Thm. 10.21]

**Proof sketch.** Rescale each orthogonal component by the inverse noise multiplier,
apply general hypercontractivity, and use orthogonality and the degree cutoff. -/
theorem product_lowDegree_norm {n k : ℕ} (P : FiniteProduct.{u} n)
    (lam q : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam) (hq : 2 < q)
    (f : P.Point → ℝ) (hdeg : P.HasDegreeLE k f) :
    P.norm q f ≤ (Real.sqrt (q - 1) * lam ^ (1 / q - 1 / 2)) ^ k * P.norm 2 f := (by
  let C : ℝ := Real.sqrt (q - 1) * lam ^ (1 / q - 1 / 2)
  have hC : 1 ≤ C := by
    apply one_le_mul_of_one_le_of_one_le
    · exact Real.one_le_sqrt.mpr (by linarith)
    · apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hlam1
      linarith [one_div_lt_one_div_of_lt (show (0 : ℝ) < 2 by norm_num) hq]
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hinv : C⁻¹ = (1 / Real.sqrt (q - 1)) * lam ^ (1 / 2 - 1 / q) := by
    dsimp [C]
    rw [mul_inv, ← Real.rpow_neg hlam.le,
      show -(1 / q - 1 / 2) = 1 / 2 - 1 / q by ring]
    simp only [one_div]
  calc
    P.norm q f = P.norm q (P.noise C⁻¹ (P.noise C f)) := by
      congr 1
      symm
      simpa only [inv_inv] using
        product_noise_inverse P C⁻¹ (inv_ne_zero hCpos.ne') f
    _ ≤ P.norm 2 (P.noise C f) :=
      (product_hypercontractivity P lam q C⁻¹ hlam hlam1 hπ hq
        (inv_nonneg.mpr hCpos.le) hinv.le (P.noise C f)).1
    _ ≤ C ^ k * P.norm 2 f := product_lowDegree_noise_norm_two P C hC f hdeg
)


/-- For an atom bound strictly below one half, a degree-`k` product function
satisfies the sharp `L¹`-to-`L²` comparison. [OD14, Thm. 10.22]

**Proof sketch.** Invert noise at the sharp discrete radius and apply
hypercontractivity together with the degree bound on the noisy second norm.
Interpolate the first and higher norms, cancel the second norm, and let
the higher exponent decrease to two using the sharp-radius comparison limit. -/
private theorem product_lowDegree_l1_l2_lt_half {n k : ℕ}
    (P : FiniteProduct.{u} n) (lam : ℝ)
    (hlam : 0 < lam) (hlamhalf : lam < 1 / 2) (hπ : P.AtomBound lam)
    (f : P.Point → ℝ) (hdeg : P.HasDegreeLE k f) :
    P.norm 2 f ≤ productNormComparisonConstant lam ^ k * P.norm 1 f :=
  (by
  apply ge_of_tendsto
    (((ComparisonAux.sharp_radius_comparison_limit lam hlam hlamhalf).pow k).mul_const
      (P.norm 1 f))
  filter_upwards [self_mem_nhdsWithin] with q hq
  let r : ℝ := sharpDiscreteRadius q lam
  have hr : 0 < r ∧ r < 1 :=
    SharpDiscrete.radius_pos_lt_one q lam hq hlam hlamhalf
  have hcoefficient : Real.exp (-(k : ℝ) * Real.log r) = (r⁻¹) ^ k := by
    rw [show -(k : ℝ) * Real.log r = (k : ℝ) * (-Real.log r) by ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log hr.1]
  have hnorm : P.norm q f ≤ Real.exp (-(k : ℝ) * Real.log r) * P.norm 2 f := by
    rw [hcoefficient]
    calc
      P.norm q f = P.norm q (P.noise r (P.noise r⁻¹ f)) :=
        (congrArg (P.norm q) (product_noise_inverse P r hr.1.ne' f)).symm
      _ ≤ P.norm 2 (P.noise r⁻¹ f) :=
        (product_hypercontractivity_sharp P lam q r hlam hlamhalf hπ hq
          hr.1.le le_rfl (P.noise r⁻¹ f)).1
      _ ≤ (r⁻¹) ^ k * P.norm 2 f :=
        product_lowDegree_noise_norm_two P r⁻¹
          ((one_le_inv₀ hr.1).2 hr.2.le) f hdeg
  have hpoint := ComparisonAux.norm_interpolation_bound P q
    (-(k : ℝ) * Real.log r) hq f hnorm
  have hexp :
      Real.exp (-(k : ℝ) * Real.log r * q / (q - 2)) =
        Real.exp (-Real.log r * q / (q - 2)) ^ k := by
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    ring
  simpa only [hexp] using hpoint
)

/-- A degree-`k` product function satisfies the sharp limiting `L¹`-to-`L²` comparison.
[OD14, Thm. 10.22] The atom bound is taken at most `1/2`; this is automatic when a
coordinate has at least two outcomes, and a smaller bound can always be chosen.

**Proof sketch.** Interpolate `L¹` with the sharp `L^(2+η)` estimate from Theorem 10.18.
Cancel the `L²` factor and take the limit as `η` decreases to zero. At atom bound
`1/2`, approach from smaller bounds and use continuity of the comparison constant. -/
theorem product_lowDegree_l1_l2 {n k : ℕ} (P : FiniteProduct.{u} n)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) (hπ : P.AtomBound lam)
    (f : P.Point → ℝ) (hdeg : P.HasDegreeLE k f) :
    P.norm 2 f ≤ productNormComparisonConstant lam ^ k * P.norm 1 f := (by
  rcases lt_or_eq_of_le hlamhalf with hlt | rfl
  · exact product_lowDegree_l1_l2_lt_half P lam hlam hlt hπ f hdeg
  haveI : Filter.NeBot
      (nhdsWithin (1 / 2 : ℝ) (Set.Ioo 0 (1 / 2))) := by
    rw [nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)]
    infer_instance
  simp only [productNormComparisonConstant]
  apply ge_of_tendsto
    ((ComparisonAux.constant_tendsto_half.pow k).mul_const (P.norm 1 f))
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact product_lowDegree_l1_l2_lt_half P a ha.1 ha.2
    (fun i x => ha.2.le.trans (hπ i x)) f hdeg
)

/-- The constant in Theorem 10.22 is at most `e/√(2lam)` throughout its range.
[OD14, Thm. 10.22]

**Proof sketch.** Take logarithms of the explicit formula and bound the resulting
logarithmic quotient; at `1/2` use its continuous extension. -/
theorem productNormComparisonConstant_le (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    productNormComparisonConstant lam ≤ Real.exp 1 / Real.sqrt (2 * lam) := (by
  by_cases hhalf : lam = 1 / 2
  · simp [hhalf, productNormComparisonConstant]
  have hnum : 0 < 1 - lam := by linarith
  have htwo : 0 < 2 * lam := by positivity
  have hgap : 0 < 2 * (1 - 2 * lam) := by
    linarith [(lt_or_eq_of_le hlamhalf).resolve_right hhalf]
  rw [productNormComparisonConstant, if_neg hhalf]
  apply (Real.log_le_log_iff
    (Real.rpow_pos_of_pos (div_pos hnum hlam) _)
    (div_pos (Real.exp_pos _) (Real.sqrt_pos.2 htwo))).mp
  rw [Real.log_rpow (div_pos hnum hlam),
    Real.log_div (Real.exp_pos 1).ne' (Real.sqrt_pos.2 htwo).ne',
    Real.log_exp, Real.log_sqrt htwo.le, one_div, inv_mul_eq_div,
    div_le_iff₀ hgap, Real.log_div hnum.ne' hlam.ne']
  have hupper := Real.log_le_sub_one_of_pos (show 0 < 2 * (1 - lam) by positivity)
  have hlower := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos htwo) htwo.le
  rw [Real.log_mul (by norm_num) hnum.ne'] at hupper
  rw [Real.log_mul (by norm_num) hlam.ne'] at hlower ⊢
  nlinarith [mul_inv_cancel₀ htwo.ne']
)

/-- A nonconstant degree-`k` product function exceeds its mean with probability at least
`(e²/(2lam))^(-k)/4`, which is at least `(15/lam)^(-k)`. [OD14, Thm. 10.23]
Positive variance expresses nonconstancy under the full-support product measure.

**Proof sketch.** Center the function. Bound the expectation of its positive part using
the `L¹`-to-`L²` inequality, and then use Cauchy–Schwarz on its positive support. -/
theorem product_oneSided_anticoncentration {n k : ℕ} (P : FiniteProduct.{u} n)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) (hπ : P.AtomBound lam)
    (f : P.Point → ℝ) (hdeg : P.HasDegreeLE k f) (hf : 0 < P.variance f) :
    (1 / 4 : ℝ) * (Real.exp 2 / (2 * lam)) ^ (-(k : ℝ)) ≤
      P.prob (fun x => P.expect f < f x) ∧
    (15 / lam) ^ (-(k : ℝ)) ≤ (1 / 4 : ℝ) * (Real.exp 2 / (2 * lam)) ^ (-(k : ℝ)) := (by
  let g : P.Point → ℝ := fun x => f x - P.expect f
  let C : ℝ := Real.exp 1 / Real.sqrt (2 * lam)
  have hC : 0 < C :=
    div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (by positivity))
  have hmean : P.expect g = 0 := by
    simp only [g, FiniteProduct.expect, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, P.mass_sum, one_mul, sub_self]
  have hconstant : 0 ≤ productNormComparisonConstant lam := by
    unfold productNormComparisonConstant
    split_ifs
    · exact (Real.exp_pos _).le
    · exact Real.rpow_nonneg (div_nonneg (by linarith) hlam.le) _
  have hnorm : P.norm 2 g ≤ C ^ k * P.norm 1 g := by
    calc
      _ ≤ productNormComparisonConstant lam ^ k * P.norm 1 g :=
        product_lowDegree_l1_l2 P lam hlam hlamhalf hπ g
          (RandomizationAux.hasDegreeLE_sub_const P f hdeg (P.expect f))
      _ ≤ C ^ k * P.norm 1 g := by
        apply mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hconstant
            (productNormComparisonConstant_le lam hlam hlamhalf) k)
        simp only [FiniteProduct.norm, div_one, Real.rpow_one, FiniteProduct.expect]
        exact Finset.sum_nonneg fun x _ =>
          mul_nonneg
            (Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le)
            (abs_nonneg _)
  have hC_sq : C ^ 2 = Real.exp 2 / (2 * lam) := by
    dsimp [C]
    rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * lam),
      ← Real.exp_nat_mul]
    norm_num
  constructor
  · have hprob := ComparisonAux.centered_probability_ge_of_norm_comparison
      P g hmean hf (C ^ k) (pow_pos hC _) hnorm
    rw [pow_right_comm, hC_sq] at hprob
    rw [Real.rpow_neg
      (div_nonneg (Real.exp_pos 2).le (show 0 ≤ 2 * lam by positivity)) (k : ℝ),
      Real.rpow_natCast]
    simpa only [g, sub_pos] using hprob
  · exact ComparisonAux.anticoncentration_coarse_lower_bound lam hlam k
      (RandomizationAux.degree_pos_of_variance_pos P f hdeg hf)
)

/-- A degree-`k` product function satisfies the coarse `q`-moment bound
with coefficient `√q`, including the endpoint `q = 2`.
[OD14, Thm. 10.24 (proof)]

**Proof sketch.** For `q > 2`, use `product_lowDegree_norm` and
`√(q - 1) ≤ √q`. At `q = 2`, the atom factor equals one and
`1 ≤ (√2) ^ k`, so the bound follows from norm nonnegativity. -/
private lemma product_lowDegree_norm_coarse {n k : ℕ}
    (P : FiniteProduct.{u} n) (lam q : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (hq : 2 ≤ q) (f : P.Point → ℝ) (hdeg : P.HasDegreeLE k f) :
    P.norm q f ≤
      (Real.sqrt q * lam ^ (1 / q - 1 / 2)) ^ k * P.norm 2 f :=
  (by
  have hf0 : 0 ≤ P.norm 2 f := by
    rw [FiniteProduct.norm, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hq with rfl | hq'
  · simpa only [sub_self, Real.rpow_zero, mul_one, one_mul] using
      mul_le_mul_of_nonneg_right
        (one_le_pow₀ (n := k)
          (Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2))) hf0
  · calc
      P.norm q f ≤
          (Real.sqrt (q - 1) * lam ^ (1 / q - 1 / 2)) ^ k * P.norm 2 f :=
        product_lowDegree_norm P lam q hlam hlam1 hπ hq' f hdeg
      _ ≤ (Real.sqrt q * lam ^ (1 / q - 1 / 2)) ^ k * P.norm 2 f := by
        apply mul_le_mul_of_nonneg_right _ hf0
        apply pow_le_pow_left₀
        · exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlam.le _)
        · exact mul_le_mul_of_nonneg_right
            (Real.sqrt_le_sqrt (by linarith : q - 1 ≤ q))
            (Real.rpow_nonneg hlam.le _)
)


/-- A nonzero degree-`k` product function has tail at most
`lam^k exp(-k lam t^(2/k)/(2e))` above `t` times its `2`-norm. [OD14, Thm. 10.24]
The explicit `k > 0` and nonzero norm assumptions resolve the reciprocal-degree and
zero-function boundary cases in the source's non-strict tail event.

**Proof sketch.** Apply Markov's inequality with the `q`-moment bound and choose
`q = lam t^(2/k)/e`; the lower bound on `t` makes this exponent at least two. -/
theorem product_lowDegree_concentration {n k : ℕ} (P : FiniteProduct.{u} n)
    (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (f : P.Point → ℝ) (hk : 0 < k) (hdeg : P.HasDegreeLE k f)
    (hf : 0 < P.norm 2 f) (t : ℝ) (ht : Real.sqrt (2 * Real.exp 1 / lam) ^ k ≤ t) :
    P.prob (fun x => t * P.norm 2 f ≤ |f x|) ≤
      lam ^ k * Real.exp (-(k : ℝ) / (2 * Real.exp 1) * lam * t ^ (2 / (k : ℝ))) := (by
  obtain ⟨ht0, hq2⟩ :=
    ConcentrationAux.scaled_concentration_parameter hk lam hlam t ht
  let q : ℝ := lam * t ^ (2 / (k : ℝ)) / Real.exp 1
  have hq : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hq2
  have hmass : ∀ x, 0 ≤ P.mass x := fun x =>
    Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le
  have hnorm : 0 ≤ P.norm q f := by
    unfold FiniteProduct.norm FiniteProduct.expect
    exact Real.rpow_nonneg
      (Finset.sum_nonneg fun x _ =>
        mul_nonneg (hmass x) (Real.rpow_nonneg (abs_nonneg _) _)) _
  calc
    P.prob (fun x => t * P.norm 2 f ≤ |f x|) ≤
        (P.norm q f / (t * P.norm 2 f)) ^ q := by
      simpa only [FiniteProduct.prob, FiniteProduct.expect,
        FiniteProduct.indicator, FiniteProduct.norm] using
        FiniteNorms.weighted_tail_le_norm_div_rpow
          P.mass hmass f q (t * P.norm 2 f) hq (mul_pos ht0 hf)
    _ ≤ ((Real.sqrt q * lam ^ (1 / q - 1 / 2)) ^ k / t) ^ q := by
      apply Real.rpow_le_rpow (div_nonneg hnorm (mul_pos ht0 hf).le) _ hq.le
      calc
        P.norm q f / (t * P.norm 2 f) ≤
            ((Real.sqrt q * lam ^ (1 / q - 1 / 2)) ^ k * P.norm 2 f) /
              (t * P.norm 2 f) :=
          div_le_div_of_nonneg_right
            (product_lowDegree_norm_coarse P lam q hlam hlam1 hπ hq2 f hdeg)
            (mul_pos ht0 hf).le
        _ = (Real.sqrt q * lam ^ (1 / q - 1 / 2)) ^ k / t :=
          mul_div_mul_right _ _ hf.ne'
    _ = lam ^ k *
        Real.exp (-(k : ℝ) / (2 * Real.exp 1) * lam * t ^ (2 / (k : ℝ))) :=
      ConcentrationAux.scaled_concentration_optimized_moment hk lam hlam t ht0
)



namespace ProductAux

/-- Noise at any rate in `[0, 1]` does not increase the second norm
of a finite-product function. [OD14, §8.3, Thm. 8.35]
The estimate applies to heterogeneous finite coordinate laws.

**Proof sketch.** Apply the proved spectral second-norm contraction
estimate, whose component multipliers have magnitude at most one. -/
theorem noise_norm_two_le {n : ℕ} (P : FiniteProduct.{u} n)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (f : P.Point → ℝ) :
    P.norm 2 (P.noise c f) ≤ P.norm 2 f :=
  (by
  exact product_noise_norm_two_le P c hc hc1 f
)

end ProductAux

end BooleanAnalysis.Hypercontractivity
