/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.ProfileCalculus
import TCSlib.BooleanAnalysis.GaussianSpace.Noise
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Joint differentiability of the bivariate Gaussian profile

## Main definitions

The existing Gaussian probability law, noise operator, and profile are reused.

## Main results

* `scalarGaussian_joint_threshold_eq_noise`.
* `contDiff_scalarGaussian_joint_threshold`.
* `differentiableAt_gaussianBivariateStability`.
* `hasFDerivAt_gaussianBivariateStability`.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
/-- The joint threshold probability is a fixed Gaussian noise average of
the corresponding cone indicator evaluated at an explicit affine shift.

**Proof sketch.** Identify two scalar Gaussians with the two-dimensional product
Gaussian law. At correlation 3/5 the noise scale is 4/5. The displayed shift
translates the fixed cone inequalities into the two threshold inequalities. -/
lemma scalarGaussian_joint_threshold_eq_noise (ρ s a b : ℝ) (hs : s ≠ 0) :
    (standardGaussianMeasure.prod standardGaussianMeasure).real
      {z : ℝ × ℝ | z.1 ≤ a ∧ ρ * z.1 + s * z.2 ≤ b} =
    gaussianNoise (3 / 5)
      ({z : Fin 2 → ℝ | z 0 ≤ 0 ∧ ρ * z 0 + s * z 1 ≤ 0}.indicator
        (1 : (Fin 2 → ℝ) → ℝ))
      ![-4 * a / 3, 4 * (ρ * a - b) / (3 * s)] := by
  let B : Set (ℝ × ℝ) := {z | z.1 ≤ a ∧ ρ * z.1 + s * z.2 ≤ b}
  have hB : MeasurableSet B := (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le (show Measurable (fun z : ℝ × ℝ => ρ * z.1 + s * z.2) by
      fun_prop) measurable_const)
  have hp := measurePreserving_finTwoArrow standardGaussianMeasure
  rw [← integral_indicator_one hB,
    ← hp.integral_comp MeasurableEquiv.finTwoArrow.measurableEmbedding
      (B.indicator (1 : ℝ × ℝ → ℝ))]
  have hsqrt : Real.sqrt (1 - (3 / 5 : ℝ) ^ 2) = 4 / 5 := by norm_num
  simp only [gaussianNoise_eq, hsqrt]
  apply integral_congr_ae
  filter_upwards [] with y
  have h0 : (3 / 5 : ℝ) * (-4 * a / 3) + (4 / 5) * y 0 ≤ 0 ↔ y 0 ≤ a := by
    constructor <;> intro h <;> nlinarith
  have heq : ρ * ((3 / 5 : ℝ) * (-4 * a / 3) + (4 / 5) * y 0) +
      s * ((3 / 5) * (4 * (ρ * a - b) / (3 * s)) + (4 / 5) * y 1) =
      (4 / 5) * (ρ * y 0 + s * y 1 - b) := by field_simp; ring
  have h1 : ρ * ((3 / 5 : ℝ) * (-4 * a / 3) + (4 / 5) * y 0) +
      s * ((3 / 5) * (4 * (ρ * a - b) / (3 * s)) + (4 / 5) * y 1) ≤ 0 ↔
      ρ * y 0 + s * y 1 ≤ b := by
    rw [heq]; constructor <;> intro h <;> nlinarith
  simp only [B, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply,
    MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  change (if y 0 ≤ a ∧ ρ * y 0 + s * y 1 ≤ b then (1 : ℝ) else 0) =
    if (3 / 5 : ℝ) * (-4 * a / 3) + (4 / 5) * y 0 ≤ 0 ∧
      ρ * ((3 / 5) * (-4 * a / 3) + (4 / 5) * y 0) +
      s * ((3 / 5) * (4 * (ρ * a - b) / (3 * s)) + (4 / 5) * y 1) ≤ 0
    then 1 else 0
  simp only [h0, h1]
/-- For nonzero conditional scale, the scalar joint Gaussian threshold
probability is smooth in its two thresholds.
[MN15, §2, regularity of the joint Gaussian probability]

**Proof sketch.** The fixed-cone representation expresses the probability as
a smooth Gaussian convolution composed with an affine map. -/
lemma contDiff_scalarGaussian_joint_threshold (ρ s : ℝ) (hs : s ≠ 0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : ℝ × ℝ =>
      (standardGaussianMeasure.prod standardGaussianMeasure).real
        {z : ℝ × ℝ | z.1 ≤ p.1 ∧ ρ * z.1 + s * z.2 ≤ p.2}) := by
  let A : Set (Fin 2 → ℝ) := {z | z 0 ≤ 0 ∧ ρ * z 0 + s * z 1 ≤ 0}
  have hA : MeasurableSet A := (measurableSet_le (measurable_pi_apply 0) measurable_const).inter
    (measurableSet_le (show Measurable (fun z : Fin 2 → ℝ => ρ * z 0 + s * z 1) by
      fun_prop) measurable_const)
  have hi : Integrable (A.indicator (1 : (Fin 2 → ℝ) → ℝ))
      (Measure.pi fun _ : Fin 2 => standardGaussianMeasure) :=
    (integrable_const (1 : ℝ)).indicator hA
  have hnoise := gaussianNoise_smooth (show (3 / 5 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num) hi
  have haff : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun p : ℝ × ℝ => ![-4 * p.1 / 3, 4 * (ρ * p.1 - p.2) / (3 * s)]) := by
    apply contDiff_pi.2
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  convert hnoise.comp haff using 1
  funext p
  exact scalarGaussian_joint_threshold_eq_noise ρ s p.1 p.2 hs
/-- The bivariate Gaussian profile is jointly differentiable at every pair
of interior volumes and interior correlation.
[MN15, §2, Lemma 2.1]

**Proof sketch.** Locally the profile is the smooth joint threshold probability
composed with the two differentiable Gaussian quantiles. -/
lemma differentiableAt_gaussianBivariateStability {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) {p : ℝ × ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun z : ℝ × ℝ => gaussianBivariateStability ρ z.1 z.2) p := by
  have hs : Real.sqrt (1 - ρ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (by nlinarith [hρ.1, hρ.2])).ne'
  have hk := (contDiff_scalarGaussian_joint_threshold ρ (Real.sqrt (1 - ρ ^ 2)) hs).differentiable (by norm_num)
  have hq : DifferentiableAt ℝ
      (fun z : ℝ × ℝ => (standardGaussianQuantile z.1, standardGaussianQuantile z.2)) p :=
    ((hasDerivAt_standardGaussianQuantile hp.1).differentiableAt.comp p
      differentiableAt_fst).prodMk
    ((hasDerivAt_standardGaussianQuantile hp.2).differentiableAt.comp p
      differentiableAt_snd)
  apply (hk.differentiableAt.comp p hq).congr_of_eventuallyEq
  have hn : Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 ∈ nhds p :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp
  filter_upwards [hn] with z hz
  exact gaussianBivariateStability_eq_threshold ρ z.1 z.2 hz.1 hz.2

/-- The derivative of the bivariate Gaussian profile is the linear functional
whose coefficients are its two conditional Gaussian cdf slopes.
[MN15, §2, Lemma 2.1]

**Proof sketch.** Joint differentiability is already known. Evaluate its
derivative on the two coordinate vectors using the scalar partial derivative
formulas, which determine the linear functional. -/
lemma hasFDerivAt_gaussianBivariateStability {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    HasFDerivAt (fun z : ℝ × ℝ => gaussianBivariateStability ρ z.1 z.2)
      (gaussianBivariateSlope ρ a b • ContinuousLinearMap.fst ℝ ℝ ℝ +
        gaussianBivariateSlope ρ b a • ContinuousLinearMap.snd ℝ ℝ ℝ) (a, b) := by
  let J : ℝ × ℝ → ℝ := fun z => gaussianBivariateStability ρ z.1 z.2
  have hd := differentiableAt_gaussianBivariateStability hρ (p := (a,b)) ⟨ha,hb⟩
  have hJ : HasFDerivAt J (fderiv ℝ J (a,b)) (a,b) := hd.hasFDerivAt
  have hleft : fderiv ℝ J (a,b) (1,0) = gaussianBivariateSlope ρ a b := by
    have hcomp : HasDerivAt (fun t => J (t,b)) (fderiv ℝ J (a,b) (1,0)) a := by
      simpa using hJ.comp_hasDerivAt a
        ((hasDerivAt_id a).prodMk (hasDerivAt_const a b))
    exact hcomp.unique (hasDerivAt_gaussianBivariateStability_left ρ hρ ha hb)
  have hright : fderiv ℝ J (a,b) (0,1) = gaussianBivariateSlope ρ b a := by
    have hcomp : HasDerivAt (fun t => J (a,t)) (fderiv ℝ J (a,b) (0,1)) b := by
      simpa using hJ.comp_hasDerivAt b
        ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))
    exact hcomp.unique (hasDerivAt_gaussianBivariateStability_right ρ hρ ha hb)
  have heq : fderiv ℝ J (a,b) =
      gaussianBivariateSlope ρ a b • ContinuousLinearMap.fst ℝ ℝ ℝ +
        gaussianBivariateSlope ρ b a • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro z
    change fderiv ℝ J (a,b) z = gaussianBivariateSlope ρ a b * z.1 +
      gaussianBivariateSlope ρ b a * z.2
    rw [realLinearFunctional_pair, hleft, hright]
    ring
  rw [heq] at hJ
  exact hJ


/-- The conditional Gaussian cdf slope is jointly differentiable at interior
volumes, for every totalized correlation. -/
lemma differentiableAt_gaussianBivariateSlope (ρ : ℝ) {p : ℝ × ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun z : ℝ × ℝ => gaussianBivariateSlope ρ z.1 z.2) p := by
  apply (hasDerivAt_standardGaussianCDF _).differentiableAt.comp p
  simpa only [div_eq_mul_inv] using
    ((((hasDerivAt_standardGaussianQuantile hp.2).differentiableAt.comp p
      differentiableAt_snd).sub
      (((hasDerivAt_standardGaussianQuantile hp.1).differentiableAt.comp p
        differentiableAt_fst).const_mul ρ)).mul_const (Real.sqrt (1 - ρ ^ 2))⁻¹)

/-- The joint derivative of the conditional cdf slope has coefficients given
by its two scalar partial derivatives. [MN15, §2, profile derivative formulas]

**Proof sketch.** Apply the chain rule to the quantiles and Gaussian cdf.
Its values on the coordinate vectors identify the derivative coefficients. -/
lemma hasFDerivAt_gaussianBivariateSlope (ρ : ℝ) {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    HasFDerivAt (fun z : ℝ × ℝ => gaussianBivariateSlope ρ z.1 z.2)
      (deriv (fun p => gaussianBivariateSlope ρ p b) a • ContinuousLinearMap.fst ℝ ℝ ℝ +
        deriv (fun p => gaussianBivariateSlope ρ a p) b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (a, b) := by
  let J : ℝ × ℝ → ℝ := fun z => gaussianBivariateSlope ρ z.1 z.2
  have hd := differentiableAt_gaussianBivariateSlope ρ (p := (a,b)) ⟨ha,hb⟩
  have hJ : HasFDerivAt J (fderiv ℝ J (a,b)) (a,b) := hd.hasFDerivAt
  have hleft : fderiv ℝ J (a,b) (1,0) =
      deriv (fun p => gaussianBivariateSlope ρ p b) a := by
    have hcomp : HasDerivAt (fun t => J (t,b)) (fderiv ℝ J (a,b) (1,0)) a := by
      simpa using hJ.comp_hasDerivAt a
        ((hasDerivAt_id a).prodMk (hasDerivAt_const a b))
    exact hcomp.deriv.symm
  have hright : fderiv ℝ J (a,b) (0,1) =
      deriv (fun p => gaussianBivariateSlope ρ a p) b := by
    have hcomp : HasDerivAt (fun t => J (a,t)) (fderiv ℝ J (a,b) (0,1)) b := by
      simpa using hJ.comp_hasDerivAt b
        ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))
    exact hcomp.deriv.symm
  have heq : fderiv ℝ J (a,b) =
      deriv (fun p => gaussianBivariateSlope ρ p b) a • ContinuousLinearMap.fst ℝ ℝ ℝ +
        deriv (fun p => gaussianBivariateSlope ρ a p) b • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro z
    change fderiv ℝ J (a,b) z =
      deriv (fun p => gaussianBivariateSlope ρ p b) a * z.1 +
      deriv (fun p => gaussianBivariateSlope ρ a p) b * z.2
    rw [realLinearFunctional_pair, hleft, hright]
    ring
  rw [heq] at hJ
  exact hJ


end BooleanAnalysis.GaussianSpace

