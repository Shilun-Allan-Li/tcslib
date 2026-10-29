/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TCSlib.BooleanAnalysis.GaussianSpace.Inputs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Taylor estimates for a single invariance replacement

## Main definitions

No additional polynomial or random-variable representation is introduced.

## Main results

* `abs_sub_taylor_le`: the Lagrange remainder at any natural order.
* `abs_sub_taylor_cubic_le`: the cubic Taylor remainder with constant `1/24`.
* `integrable_test_of_memLp`: integrability of tests with a bounded highest derivative.
* `integrable_test_of_memLp_four`: the fourth-order specialization.
* `integral_taylor_polynomial`: integration of a finite Taylor polynomial.
* `integral_taylor_cubic`: the common expected cubic Taylor polynomial.
* `abs_integral_sub_taylor_polynomial_le`: the expected remainder at any natural order.
* `abs_integral_sub_taylor_le`: the fourth-order expected remainder.
* `affine_replacement_bound_c3`: third-order comparison with matching first two moments.
* `affine_replacement_bound`: comparison of two affine scalar inputs with matching moments.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, proof of the Basic Invariance Principle (11.29).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BooleanAnalysis.GaussianSpace

/-- A test with bounded derivative of order `m + 1` differs from its Taylor
polynomial of order `m` by at most `C |b|^(m+1)/(m+1)!`.
[OD14, §11.5–11.6, Taylor remainder in the replacement argument]

**Proof sketch.** Apply the Lagrange remainder on `[0,1]` to the affine
reparametrization of the test. The chain rule supplies each power of the increment. -/
theorem abs_sub_taylor_le
    (m : ℕ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (m + 1) ψ)
    (C : ℝ) (hC : ∀ t, |iteratedDeriv (m + 1) ψ t| ≤ C)
    (a b : ℝ) :
    |ψ (a + b) - ∑ j ∈ Finset.range (m + 1),
      (iteratedDeriv j ψ a / (j.factorial : ℝ)) * b ^ j| ≤
      (C / ((m + 1).factorial : ℝ)) * |b| ^ (m + 1) := by
  let g : ℝ → ℝ := fun t => ψ (a + b * t)
  have hg : ContDiff ℝ (m + 1) g := by dsimp [g]; fun_prop
  have hd (j : ℕ) (hj : j ≤ m + 1) (t : ℝ) :
      iteratedDeriv j g t = b ^ j * iteratedDeriv j ψ (a + b * t) := by
    have hshift : ContDiff ℝ j (fun z => ψ (a + z)) :=
      (hψ.of_le (by exact_mod_cast hj)).comp (by fun_prop)
    change iteratedDeriv j (fun t => (fun z => ψ (a + z)) (b * t)) t = _
    rw [iteratedDeriv_comp_const_mul hshift, iteratedDeriv_comp_const_add]
  have ht : taylorWithinEval g m (Set.Icc 0 1) 0 1 =
      ∑ j ∈ Finset.range (m + 1),
        (iteratedDeriv j ψ a / (j.factorial : ℝ)) * b ^ j := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j ≤ m + 1 := (Finset.mem_range.mp hj).le
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      ((hg.of_le (by exact_mod_cast hjm)).contDiffAt) (by simp), hd j hjm 0]
    simp [smul_eq_mul, div_eq_mul_inv]
    ring
  obtain ⟨t, htI, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := g) (n := m) (x₀ := 0) (x := 1) (by norm_num) hg.contDiffOn
  rw [ht, hd (m + 1) le_rfl t] at he
  have hrem : ψ (a + b) - ∑ j ∈ Finset.range (m + 1),
      (iteratedDeriv j ψ a / (j.factorial : ℝ)) * b ^ j =
        b ^ (m + 1) * iteratedDeriv (m + 1) ψ (a + b * t) /
          ((m + 1).factorial : ℝ) := by
    simpa [g] using he
  rw [hrem, abs_div, abs_mul, abs_pow, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ ((m + 1).factorial : ℝ))]
  calc
    _ ≤ |b| ^ (m + 1) * C / ((m + 1).factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hC _) (by positivity)) (by positivity)
    _ = _ := by ring

/-- A four-times continuously differentiable real function whose fourth derivative
is bounded by `C` differs from its cubic Taylor polynomial by at most `C b⁴ / 24`.
[OD14, §11.6, proof of the Basic Invariance Principle]

**Proof sketch.** Apply Taylor's theorem with Lagrange remainder on `[0,1]` to
the function `t ↦ ψ (a + b*t)`. Its `j`th derivative is
`b^j * ψ⁽ʲ⁾ (a + b*t)`. The cubic Taylor polynomial at zero gives the
displayed sum, and the fourth derivative is bounded by `C*b⁴`.
This also handles increments of either sign, including zero. -/
theorem abs_sub_taylor_cubic_le
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ)
    (C : ℝ) (_hC0 : 0 ≤ C)
    (hC : ∀ t, |iteratedDeriv 4 ψ t| ≤ C)
    (a b : ℝ) :
    |ψ (a + b) -
      ∑ j ∈ Finset.range 4,
        (iteratedDeriv j ψ a / (j.factorial : ℝ)) * b ^ j| ≤
      (C / 24) * b ^ 4 :=
  (abs_sub_taylor_le 3 ψ hψ C hC a b).trans_eq
    (by simp [Nat.factorial, ← abs_pow, abs_of_nonneg (show 0 ≤ b ^ 4 by positivity)])

/-- A test whose derivative of order `m + 1` is bounded is integrable on any
random variable with a finite moment of that order.
[OD14, §11.5–11.6, integrability in the Taylor replacement argument]

**Proof sketch.** Taylor expansion at zero bounds the test by an integrable
polynomial and a constant times the absolute moment of order `m + 1`. -/
theorem integrable_test_of_memLp
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (m : ℕ) {Z : Ω → ℝ} (hZ : MemLp Z ((m + 1 : ℕ) : ℝ≥0∞) μ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (m + 1) ψ)
    (C : ℝ) (hC : ∀ t, |iteratedDeriv (m + 1) ψ t| ≤ C) :
    Integrable (fun ω => ψ (Z ω)) μ := by
  have hpow (j : ℕ) (hj : j ≤ m + 1) : Integrable (fun ω => Z ω ^ j) μ := by
    simpa using Hypercontractivity.integrable_mul_pow_of_memLp
      (p := m + 1) (a := j) (b := 0) hZ hZ (by omega)
  let P : Ω → ℝ := fun ω => ∑ j ∈ Finset.range (m + 1),
    (iteratedDeriv j ψ 0 / (j.factorial : ℝ)) * Z ω ^ j
  have hP : Integrable P μ :=
    integrable_finset_sum _ (fun j hj =>
      (hpow j (Finset.mem_range.mp hj).le).const_mul _)
  refine (hP.norm.add (hZ.integrable_norm_pow'.const_mul
    (C / ((m + 1).factorial : ℝ)))).mono'
    (hψ.continuous.comp_aestronglyMeasurable hZ.aestronglyMeasurable) ?_
  filter_upwards [] with ω
  calc
    ‖ψ (Z ω)‖ ≤ ‖ψ (Z ω) - P ω‖ + ‖P ω‖ := by
      simpa only [sub_add_cancel] using norm_add_le (ψ (Z ω) - P ω) (P ω)
    _ ≤ (C / ((m + 1).factorial : ℝ)) * ‖Z ω‖ ^ (m + 1) + ‖P ω‖ := by
      apply add_le_add_right
      simpa only [Real.norm_eq_abs, zero_add, P] using
        abs_sub_taylor_le m ψ hψ C hC 0 (Z ω)
    _ = ‖P ω‖ + (C / ((m + 1).factorial : ℝ)) * ‖Z ω‖ ^ (m + 1) := add_comm _ _

/-- A `C⁴` test with bounded fourth derivative is integrable on every real random
variable with finite fourth moment. [OD14, §11.6, proof of (11.29)] -/
theorem integrable_test_of_memLp_four
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 4 μ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ)
    (C : ℝ) (_hC0 : 0 ≤ C)
    (hC : ∀ t, |iteratedDeriv 4 ψ t| ≤ C) :
    Integrable (fun ω => ψ (Z ω)) μ :=
  integrable_test_of_memLp 3 hZ ψ hψ C hC

/-- Integrating a Taylor polynomial gives the corresponding linear combination
of input moments. This is technical integration glue for the replacement argument. -/
theorem integral_taylor_polynomial
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℕ} (X : Ω → ℝ) (hX : MemLp X (p : ℝ≥0∞) μ)
    (m : ℕ) (hm : m ≤ p) (ψ : ℝ → ℝ) (a b : ℝ) :
    (∫ ω, ∑ j ∈ Finset.range m,
      (iteratedDeriv j ψ a / (j.factorial : ℝ)) * (b * X ω) ^ j ∂μ) =
      ∑ j ∈ Finset.range m,
        ((iteratedDeriv j ψ a / (j.factorial : ℝ)) * b ^ j) *
          ∫ ω, X ω ^ j ∂μ := by
  simp_rw [mul_pow, ← mul_assoc]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]
  · intro j hj
    have hpow : Integrable (fun ω => X ω ^ j) μ := by
      simpa using Hypercontractivity.integrable_mul_pow_of_memLp
        (p := p) (a := j) (b := 0) hX hX (by
          have := Finset.mem_range.mp hj
          omega)
    exact hpow.const_mul _

/-- The expected cubic Taylor polynomial of `ψ (a + bX)` is
`ψ a + ψ'' a * b² / 2` for an input satisfying Hypothesis 11.65.
[OD14, §11.6, proof of the Basic Invariance Principle (11.29)]
The derivative values are fixed coefficients, so no smoothness assumption is needed.

**Proof sketch.** Integrate the four polynomial terms. The first and third
moments vanish, the second is one, and the measure has total mass one. -/
theorem integral_taylor_cubic
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : HasInvarianceMoments X μ)
    (ψ : ℝ → ℝ) (a b : ℝ) :
    (∫ ω, ∑ j ∈ Finset.range 4,
      (iteratedDeriv j ψ a / (j.factorial : ℝ)) * (b * X ω) ^ j ∂μ) =
      ψ a + (iteratedDeriv 2 ψ a / 2) * b ^ 2 := by
  rw [integral_taylor_polynomial X hX.reasonable.memLp 4 le_rfl]
  norm_num [Finset.sum_range_succ, hX.mean, hX.second, hX.third]

/-- The expected Taylor remainder is bounded by the corresponding absolute
input moment. [OD14, §11.5–11.6, Taylor replacement argument]

**Proof sketch.** Integrate the pointwise Lagrange remainder. All Taylor terms
and the remainder bound are integrable by the finite moment assumption. -/
theorem abs_integral_sub_taylor_polynomial_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (m : ℕ) (X : Ω → ℝ) (hX : MemLp X ((m + 1 : ℕ) : ℝ≥0∞) μ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (m + 1) ψ)
    (C : ℝ) (hC : ∀ t, |iteratedDeriv (m + 1) ψ t| ≤ C) (a b : ℝ) :
    |(∫ ω, ψ (a + b * X ω) ∂μ) -
      (∫ ω, ∑ j ∈ Finset.range (m + 1),
        (iteratedDeriv j ψ a / (j.factorial : ℝ)) * (b * X ω) ^ j ∂μ)| ≤
      (C / ((m + 1).factorial : ℝ)) * |b| ^ (m + 1) *
        (∫ ω, |X ω| ^ (m + 1) ∂μ) := by
  have hpow (j : ℕ) (hj : j ≤ m + 1) :
      Integrable (fun ω => (b * X ω) ^ j) μ := by
    simpa using Hypercontractivity.integrable_mul_pow_of_memLp
      (p := m + 1) (a := j) (b := 0)
      (hX.const_mul b) (hX.const_mul b) (by omega)
  let P : Ω → ℝ := fun ω => ∑ j ∈ Finset.range (m + 1),
    (iteratedDeriv j ψ a / (j.factorial : ℝ)) * (b * X ω) ^ j
  have hP : Integrable P μ :=
    integrable_finset_sum _ (fun j hj =>
      (hpow j (Finset.mem_range.mp hj).le).const_mul _)
  have htest : Integrable (fun ω => ψ (a + b * X ω)) μ :=
    integrable_test_of_memLp m ((memLp_const a).add (hX.const_mul b)) ψ hψ C hC
  have hbound : Integrable
      (fun ω => (C / ((m + 1).factorial : ℝ)) * |b * X ω| ^ (m + 1)) μ := by
    simpa only [Real.norm_eq_abs] using
      (hX.const_mul b).integrable_norm_pow'.const_mul (C / ((m + 1).factorial : ℝ))
  rw [← integral_sub htest hP]
  calc
    _ ≤ ∫ ω, |ψ (a + b * X ω) - P ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (C / ((m + 1).factorial : ℝ)) * |b * X ω| ^ (m + 1) ∂μ := by
      apply integral_mono_ae (htest.sub hP).abs hbound
      exact Filter.Eventually.of_forall fun ω =>
        abs_sub_taylor_le m ψ hψ C hC a (b * X ω)
    _ = _ := by
      simp_rw [abs_mul, mul_pow, ← mul_assoc, integral_const_mul]

/-- For an input satisfying Hypothesis 11.65, the expected test of `a + bX`
differs from its expected cubic Taylor polynomial by at most `3C b⁴ / 8`.
[OD14, §11.6, proof of the Basic Invariance Principle (11.29)]

**Proof sketch.** Integrate the pointwise Taylor remainder. The fourth moment
of the input is at most nine, so the bound is `9C b⁴ / 24`. -/
theorem abs_integral_sub_taylor_le
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : HasInvarianceMoments X μ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, |iteratedDeriv 4 ψ t| ≤ C) (a b : ℝ) :
    |(∫ ω, ψ (a + b * X ω) ∂μ) -
      (ψ a + (iteratedDeriv 2 ψ a / 2) * b ^ 2)| ≤
      (3 * C / 8) * b ^ 4 := by
  have hfourth : (∫ ω, X ω ^ 4 ∂μ) ≤ 9 := by
    simpa only [moment, Pi.pow_apply, hX.second, one_pow, mul_one] using
      hX.reasonable.moment_le
  have h := abs_integral_sub_taylor_polynomial_le
    3 X hX.reasonable.memLp ψ hψ C hC a b
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at h
  simp only [(by decide : Even 4).pow_abs] at h
  rw [integral_taylor_cubic X hX ψ a b] at h
  calc
    _ ≤ (C / 24) * b ^ 4 * (∫ ω, X ω ^ 4 ∂μ) := h
    _ ≤ (C / 24) * b ^ 4 * 9 :=
      mul_le_mul_of_nonneg_left hfourth (by positivity)
    _ = _ := by ring

/-- Replacing scalar inputs with matching first and second moments changes a
`C³` test by at most its Taylor constant times their third absolute moments.
[OD14, §11.5, Invariance Principle for Sums; Remark 11.66]

**Proof sketch.** The expected quadratic Taylor polynomials agree. Bound each
cubic remainder by its absolute moment, then add the two errors. -/
theorem affine_replacement_bound_c3
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ξ → ℝ) (hX : MemLp X 3 μ) (hY : MemLp Y 3 ν)
    (hmean : (∫ ω, X ω ∂μ) = ∫ ω, Y ω ∂ν)
    (hsecond : (∫ ω, X ω ^ 2 ∂μ) = ∫ ω, Y ω ^ 2 ∂ν)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 3 ψ)
    (C : ℝ) (hC : ∀ t, |iteratedDeriv 3 ψ t| ≤ C) (a b : ℝ) :
    |(∫ ω, ψ (a + b * X ω) ∂μ) - (∫ ω, ψ (a + b * Y ω) ∂ν)| ≤
      (C / 6) * |b| ^ 3 *
        ((∫ ω, |X ω| ^ 3 ∂μ) + ∫ ω, |Y ω| ^ 3 ∂ν) := by
  have hpoly :
      (∫ ω, ∑ j ∈ Finset.range 3,
        (iteratedDeriv j ψ a / (j.factorial : ℝ)) * (b * X ω) ^ j ∂μ) =
      (∫ ω, ∑ j ∈ Finset.range 3,
        (iteratedDeriv j ψ a / (j.factorial : ℝ)) * (b * Y ω) ^ j ∂ν) := by
    rw [integral_taylor_polynomial X hX 3 le_rfl,
      integral_taylor_polynomial Y hY 3 le_rfl]
    norm_num [Finset.sum_range_succ, hmean, hsecond]
  have hRX := abs_integral_sub_taylor_polynomial_le 2 X hX ψ hψ C hC a b
  have hRY := abs_integral_sub_taylor_polynomial_le 2 Y hY ψ hψ C hC a b
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at hRX hRY
  rw [← hpoly] at hRY
  calc
    _ ≤ |(∫ ω, ψ (a + b * X ω) ∂μ) -
          (∫ ω, ∑ j ∈ Finset.range 3,
            (iteratedDeriv j ψ a / (j.factorial : ℝ)) * (b * X ω) ^ j ∂μ)| +
        |(∫ ω, ∑ j ∈ Finset.range 3,
            (iteratedDeriv j ψ a / (j.factorial : ℝ)) * (b * X ω) ^ j ∂μ) -
          (∫ ω, ψ (a + b * Y ω) ∂ν)| := abs_sub_le _ _ _
    _ ≤ (C / 6) * |b| ^ 3 * (∫ ω, |X ω| ^ 3 ∂μ) +
        (C / 6) * |b| ^ 3 * (∫ ω, |Y ω| ^ 3 ∂ν) := by
      exact add_le_add hRX (by simpa only [abs_sub_comm] using hRY)
    _ = _ := by ring

/-- Replacing one scalar input satisfying Hypothesis 11.65 by another changes
the expected test of `a + bX` by at most `3C b⁴ / 4`.
[OD14, §11.6, proof of the Basic Invariance Principle (11.29)]

**Proof sketch.** The moments through order three agree, so the expected cubic
Taylor polynomials at `a` agree. Each fourth-order remainder contributes at most
`(C/24) b⁴ E[X⁴]`, which is at most `9C b⁴ / 24`. Add the two remainders. -/
theorem affine_replacement_bound
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ξ → ℝ)
    (hX : HasInvarianceMoments X μ) (hY : HasInvarianceMoments Y ν)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, |iteratedDeriv 4 ψ t| ≤ C) (a b : ℝ) :
    |(∫ ω, ψ (a + b * X ω) ∂μ) - (∫ ω, ψ (a + b * Y ω) ∂ν)| ≤
      (3 * C / 4) * b ^ 4 := by
  calc
    _ ≤ |(∫ ω, ψ (a + b * X ω) ∂μ) -
          (ψ a + (iteratedDeriv 2 ψ a / 2) * b ^ 2)| +
        |(ψ a + (iteratedDeriv 2 ψ a / 2) * b ^ 2) -
          (∫ ω, ψ (a + b * Y ω) ∂ν)| := abs_sub_le _ _ _
    _ ≤ (3 * C / 8) * b ^ 4 + (3 * C / 8) * b ^ 4 := by
      apply add_le_add
      · exact abs_integral_sub_taylor_le X hX ψ hψ C hC0 hC a b
      · rw [abs_sub_comm]
        exact abs_integral_sub_taylor_le Y hY ψ hψ C hC0 hC a b
    _ = _ := by ring

end BooleanAnalysis.GaussianSpace
