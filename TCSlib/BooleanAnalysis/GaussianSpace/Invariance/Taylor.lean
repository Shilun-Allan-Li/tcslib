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

* `abs_sub_taylor_cubic_le`: the cubic Taylor remainder with constant `1/24`.
* `integrable_test_of_memLp_four`: integrability of a test with bounded fourth derivative.
* `integral_taylor_cubic`: the common expected cubic Taylor polynomial.
* `abs_integral_sub_taylor_le`: the expected remainder for one scalar input.
* `affine_replacement_bound`: comparison of two affine scalar inputs with matching moments.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, proof of the Basic Invariance Principle (11.29).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

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
      (C / 24) * b ^ 4 := by
  let g : ℝ → ℝ := fun t => ψ (a + b * t)
  have hg : ContDiff ℝ 4 g := by dsimp [g]; fun_prop
  have hd (j : ℕ) (hj : j ≤ 4) (t : ℝ) :
      iteratedDeriv j g t = b ^ j * iteratedDeriv j ψ (a + b * t) := by
    have hshift : ContDiff ℝ j (fun z => ψ (a + z)) :=
      (hψ.of_le (by exact_mod_cast hj)).comp (by fun_prop)
    change iteratedDeriv j (fun t => (fun z => ψ (a + z)) (b * t)) t = _
    rw [iteratedDeriv_comp_const_mul hshift, iteratedDeriv_comp_const_add]
  have ht : taylorWithinEval g 3 (Set.Icc 0 1) 0 1 =
      ∑ j ∈ Finset.range 4, (iteratedDeriv j ψ a / (j.factorial : ℝ)) * b ^ j := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hj4 : j ≤ 4 := (Finset.mem_range.mp hj).le
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      ((hg.of_le (by exact_mod_cast hj4)).contDiffAt) (by simp),
      hd j hj4 0]
    simp [smul_eq_mul, div_eq_mul_inv]
    ring
  obtain ⟨t, htI, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := g) (n := 3) (x₀ := 0) (x := 1) (by norm_num) hg.contDiffOn
  rw [ht, hd 4 (by omega) t] at he
  have hrem : ψ (a + b) - ∑ j ∈ Finset.range 4,
      (iteratedDeriv j ψ a / (j.factorial : ℝ)) * b ^ j =
        b ^ 4 * iteratedDeriv 4 ψ (a + b * t) / 24 := by
    simpa [g] using he
  rw [hrem]
  calc
    _ = (b ^ 4 / 24) * |iteratedDeriv 4 ψ (a + b * t)| := by
      rw [abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ b ^ 4)]
      norm_num
      ring
    _ ≤ (b ^ 4 / 24) * C :=
      mul_le_mul_of_nonneg_left (hC _) (by positivity)
    _ = _ := by ring

/-- A `C⁴` test with bounded fourth derivative is integrable on every real random
variable with finite fourth moment. [OD14, §11.6, proof of (11.29)]

**Proof sketch.** Taylor expansion at zero splits the test into a cubic polynomial
and a remainder bounded by a constant times the fourth power. All these terms
are integrable under the fourth-moment assumption. -/
theorem integrable_test_of_memLp_four
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 4 μ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, |iteratedDeriv 4 ψ t| ≤ C) :
    Integrable (fun ω => ψ (Z ω)) μ := by
  have hpow (j : ℕ) (hj : j ≤ 4) : Integrable (fun ω => Z ω ^ j) μ := by
    simpa using Hypercontractivity.integrable_mul_pow_of_memLp
      (p := 4) (a := j) (b := 0) hZ hZ (by omega)
  let P : Ω → ℝ := fun ω => ∑ j ∈ Finset.range 4,
    (iteratedDeriv j ψ 0 / (j.factorial : ℝ)) * Z ω ^ j
  have hP : Integrable P μ :=
    integrable_finset_sum _ (fun j hj =>
      (hpow j (Finset.mem_range.mp hj).le).const_mul _)
  refine (hP.norm.add ((hpow 4 le_rfl).const_mul (C / 24))).mono'
    (hψ.continuous.comp_aestronglyMeasurable hZ.aestronglyMeasurable) ?_
  filter_upwards [] with ω
  calc
    ‖ψ (Z ω)‖ ≤ ‖ψ (Z ω) - P ω‖ + ‖P ω‖ := by
      simpa only [sub_add_cancel] using norm_add_le (ψ (Z ω) - P ω) (P ω)
    _ ≤ (C / 24) * Z ω ^ 4 + ‖P ω‖ := by
      apply add_le_add_right
      simpa only [Real.norm_eq_abs, zero_add, P] using
        abs_sub_taylor_cubic_le ψ hψ C hC0 hC 0 (Z ω)
    _ = ‖P ω‖ + (C / 24) * Z ω ^ 4 := add_comm _ _

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
  have hpow (j : ℕ) (hj : j ≤ 4) : Integrable (fun ω => X ω ^ j) μ := by
    simpa using Hypercontractivity.integrable_mul_pow_of_memLp
      (p := 4) (a := j) (b := 0)
      hX.reasonable.memLp hX.reasonable.memLp (by omega)
  calc
    _ = ∑ j ∈ Finset.range 4,
        ((iteratedDeriv j ψ a / (j.factorial : ℝ)) * b ^ j) *
          ∫ ω, X ω ^ j ∂μ := by
      simp_rw [mul_pow, ← mul_assoc]
      rw [integral_finset_sum]
      · simp_rw [integral_const_mul]
      · intro j hj
        exact (hpow j (Finset.mem_range.mp hj).le).const_mul _
    _ = _ := by
      norm_num [Finset.sum_range_succ, hX.mean, hX.second, hX.third]

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
  have hpow (j : ℕ) (hj : j ≤ 4) : Integrable (fun ω => (b * X ω) ^ j) μ := by
    simpa using Hypercontractivity.integrable_mul_pow_of_memLp
      (p := 4) (a := j) (b := 0)
      (hX.reasonable.memLp.const_mul b) (hX.reasonable.memLp.const_mul b) (by omega)
  let P : Ω → ℝ := fun ω => ∑ j ∈ Finset.range 4,
    (iteratedDeriv j ψ a / (j.factorial : ℝ)) * (b * X ω) ^ j
  have hP : Integrable P μ :=
    integrable_finset_sum _ (fun j hj =>
      (hpow j (Finset.mem_range.mp hj).le).const_mul _)
  have htest : Integrable (fun ω => ψ (a + b * X ω)) μ :=
    integrable_test_of_memLp_four
      ((memLp_const a).add (hX.reasonable.memLp.const_mul b)) ψ hψ C hC0 hC
  have hfourth : (∫ ω, X ω ^ 4 ∂μ) ≤ 9 := by
    simpa only [moment, Pi.pow_apply, hX.second, one_pow, mul_one] using
      hX.reasonable.moment_le
  rw [← integral_taylor_cubic X hX ψ a b, ← integral_sub htest hP]
  calc
    _ ≤ ∫ ω, |ψ (a + b * X ω) - P ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (C / 24) * (b * X ω) ^ 4 ∂μ := by
      apply integral_mono_ae (htest.sub hP).abs ((hpow 4 le_rfl).const_mul (C / 24))
      exact Filter.Eventually.of_forall fun ω =>
        abs_sub_taylor_cubic_le ψ hψ C hC0 hC a (b * X ω)
    _ = (C / 24) * b ^ 4 * (∫ ω, X ω ^ 4 ∂μ) := by
      simp_rw [mul_pow, ← mul_assoc, integral_const_mul]
    _ ≤ (C / 24) * b ^ 4 * 9 :=
      mul_le_mul_of_nonneg_left hfourth (by positivity)
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
