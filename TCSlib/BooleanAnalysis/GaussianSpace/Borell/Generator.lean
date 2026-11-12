/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.MehlerDifferentiation
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.SpatialDifferentiation
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Integration
import Mathlib.Analysis.Calculus.Deriv.Pi
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Ornstein–Uhlenbeck generator of Gaussian averaging

## Main definitions

The Gaussian noise operator and its spatial derivatives are reused.

## Main results

* `hasDerivAt_gaussianNoise_exp_neg_generator`: the Mehler average at time t
  solves the Ornstein–Uhlenbeck equation for bounded C2 initial data with
  bounded first and second derivatives.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
/-- Gaussian integration by parts converts the noise-coordinate factor in
a Mehler-averaged directional derivative to the scaled second derivative.
[MN15, §2, generator calculation]

**Proof sketch.** Differentiate the coordinate derivative along the affine
Gaussian endpoint. Bounded derivatives and the finite Gaussian first moment
supply the three integrability hypotheses for coordinate integration by parts. -/
lemma integral_coordinate_fderiv_mehler {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {M K : ℝ}
    (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (hk : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K)
    (r s : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    (∫ y, y i * fderiv ℝ f (r • x + s • y) (Pi.single i 1)
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) =
    s * ∫ y, fderiv ℝ (fderiv ℝ f) (r • x + s • y) (Pi.single i 1) (Pi.single i 1)
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  let u := fun y : Fin n → ℝ => fderiv ℝ f (r • x + s • y) (Pi.single i 1)
  let v := fun y : Fin n → ℝ =>
    s * fderiv ℝ (fderiv ℝ f) (r • x + s • y) (Pi.single i 1) (Pi.single i 1)
  have hucont : Continuous u :=
    ((hf.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply continuous_const
  have hHcont : Continuous (fun y : Fin n → ℝ => fderiv ℝ (fderiv ℝ f) (r • x + s • y)) :=
    ((hf.fderiv_right (by norm_num)).continuous_fderiv le_rfl).comp (by fun_prop)
  have hvcont : Continuous v :=
    continuous_const.mul ((hHcont.clm_apply continuous_const).clm_apply continuous_const)
  have huB (y) : ‖u y‖ ≤ M := by
    calc
      _ ≤ ‖fderiv ℝ f (r • x + s • y)‖ * ‖(Pi.single i (1:ℝ) : Fin n → ℝ)‖ := (fderiv ℝ f _).le_opNorm _
      _ = ‖fderiv ℝ f (r • x + s • y)‖ := by rw [Pi.norm_single, norm_one, mul_one]
      _ ≤ M := hm _
  have hvB (y) : ‖v y‖ ≤ |s| * K := by
    rw [show v y = s * fderiv ℝ (fderiv ℝ f) (r • x + s • y) (Pi.single i 1) (Pi.single i 1) from rfl,
      norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg s)
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) (r • x + s • y) (Pi.single i 1)‖ * ‖(Pi.single i (1:ℝ) : Fin n → ℝ)‖ :=
        (fderiv ℝ (fderiv ℝ f) (r • x + s • y) (Pi.single i 1)).le_opNorm (Pi.single i 1)
      _ ≤ (‖fderiv ℝ (fderiv ℝ f) (r • x + s • y)‖ * ‖(Pi.single i (1:ℝ) : Fin n → ℝ)‖) *
          ‖(Pi.single i (1:ℝ) : Fin n → ℝ)‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ f) (r • x + s • y)).le_opNorm (Pi.single i 1)) (norm_nonneg _)
      _ = ‖fderiv ℝ (fderiv ℝ f) (r • x + s • y)‖ := by rw [Pi.norm_single, norm_one, mul_one, mul_one]
      _ ≤ K := hk _
  have hu := Integrable.of_bound (μ := Measure.pi fun _ : Fin n => standardGaussianMeasure) hucont.aestronglyMeasurable M (Eventually.of_forall huB)
  have hv := Integrable.of_bound (μ := Measure.pi fun _ : Fin n => standardGaussianMeasure) hvcont.aestronglyMeasurable (|s| * K) (Eventually.of_forall hvB)
  have hnorm : Integrable (fun y : Fin n → ℝ => ‖y‖)
      (Measure.pi fun _ => standardGaussianMeasure) := by
    simpa only [pow_one] using (integrable_gaussianPi_norm_pow (n := n) 1)
  have hxu : Integrable (fun y => y i * u y)
      (Measure.pi fun _ => standardGaussianMeasure) := by
    apply (hnorm.mul_const M).mono' (by fun_prop)
    exact Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i)
        (huB y) (norm_nonneg _) (norm_nonneg _)
  have hd (y : Fin n → ℝ) :
      HasDerivAt (fun t => u (Function.update y i t)) (v y) (y i) := by
    have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    have hd := (hdf.differentiable le_rfl
      (r • x + s • Function.update y i (y i))).hasFDerivAt.comp_hasDerivAt (y i)
        (((hasDerivAt_update y i (y i)).const_smul s).const_add (r • x))
    have he := hd.clm_apply (hasDerivAt_const (y i) ((Pi.single i (1:ℝ) : Fin n → ℝ)))
    simpa [u, v, Function.update_eq_self, smul_eq_mul] using he
  have hh := integral_coordinate_derivative_gaussianPi i u v hd hu hv hxu
  rw [integral_const_mul] at hh
  exact hh.symm

/-- A uniformly bounded continuous family of linear functionals applied to
a continuous Gaussian-integrable vector field is integrable. -/
private lemma integrable_gaussianPi_clm_apply {n : ℕ}
    (L : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
    (hL : Continuous L) {M : ℝ} (hM : ∀ y, ‖L y‖ ≤ M)
    (v : (Fin n → ℝ) → (Fin n → ℝ)) (hv : Continuous v)
    (hvn : Integrable (fun y => ‖v y‖)
      (Measure.pi fun _ : Fin n => standardGaussianMeasure)) :
    Integrable (fun y => L y (v y))
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  apply (hvn.const_mul M).mono' (hL.clm_apply hv).aestronglyMeasurable
  exact Eventually.of_forall fun y =>
    ((L y).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _))

/-- The Gaussian average of a Mehler derivative evaluated on the noise
vector is the noise scale times the averaged Hessian trace.
[MN15, §2, generator calculation]

**Proof sketch.** Expand the noise vector in coordinate directions, interchange
the finite sum and integral, and apply coordinate Gaussian integration by parts. -/
lemma integral_fderiv_mehler_apply_self {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {M K : ℝ}
    (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (hk : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K)
    (r s : ℝ) (x : Fin n → ℝ) :
    (∫ y, fderiv ℝ f (r • x + s • y) y
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) =
    s * ∑ i, ∫ y, fderiv ℝ (fderiv ℝ f) (r • x + s • y) (Pi.single i 1) (Pi.single i 1)
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  have hnorm : Integrable (fun y : Fin n → ℝ => ‖y‖)
      (Measure.pi fun _ => standardGaussianMeasure) := by
    simpa only [pow_one] using (integrable_gaussianPi_norm_pow (n := n) 1)
  have hLi (i : Fin n) : Integrable
      (fun y : Fin n → ℝ => y i * fderiv ℝ f (r • x + s • y) (Pi.single i 1))
      (Measure.pi fun _ => standardGaussianMeasure) := by
    apply (hnorm.mul_const M).mono' (by fun_prop)
    exact Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_eq_abs]
      apply mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i) _ (norm_nonneg _) (norm_nonneg _)
      calc
        _ ≤ ‖fderiv ℝ f (r • x + s • y)‖ * ‖(Pi.single i 1 : Fin n → ℝ)‖ := (fderiv ℝ f _).le_opNorm _
        _ = ‖fderiv ℝ f (r • x + s • y)‖ := by rw [Pi.norm_single, norm_one, mul_one]
        _ ≤ M := hm _
  calc
    _ = ∫ y, ∑ i, y i * fderiv ℝ f (r • x + s • y) (Pi.single i 1)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
      integral_congr_ae (Eventually.of_forall fun y => realLinearFunctional_pi _ y)
    _ = _ := by
      rw [integral_finset_sum _ (fun i _ => hLi i), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_coordinate_fderiv_mehler hf hm hk r s x i

/-- The correlation derivative of Gaussian noise equals the averaged gradient
evaluated on the starting point minus the correlation times the averaged
Hessian trace. [MN15, §2, generator calculation]

**Proof sketch.** Differentiate the Mehler integral in the correlation.
Linearity splits the endpoint velocity into its starting-point and noise
parts. Gaussian integration by parts turns the noise part into the trace. -/
lemma hasDerivAt_gaussianNoise_correlation_generator {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {B M K : ℝ}
    (hb : ∀ z, |f z| ≤ B) (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (hk : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K)
    (x : Fin n → ℝ) {r : ℝ} (hr : r ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun q => gaussianNoise q f x)
      ((∫ y, fderiv ℝ f (r • x + Real.sqrt (1-r^2) • y) x
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) -
        r * ∑ i, ∫ y, fderiv ℝ (fderiv ℝ f)
          (r • x + Real.sqrt (1-r^2) • y) (Pi.single i 1) (Pi.single i 1)
          ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) r := by
  let s := Real.sqrt (1-r^2)
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr (by
    nlinarith [mul_pos (sub_pos.mpr hr.2) (sub_pos.mpr hr.1)])).ne'
  let L := fun y : Fin n → ℝ => fderiv ℝ f (r • x + s • y)
  have hLc : Continuous L := (hf.continuous_fderiv (by norm_num)).comp (by fun_prop)
  have hLM (y) : ‖L y‖ ≤ M := hm _
  have hnorm : Integrable (fun y : Fin n → ℝ => ‖y‖)
      (Measure.pi fun _ => standardGaussianMeasure) := by
    simpa only [pow_one] using (integrable_gaussianPi_norm_pow (n := n) 1)
  have hLy := integrable_gaussianPi_clm_apply L hLc hLM id continuous_id hnorm
  have hLx := integrable_gaussianPi_clm_apply L hLc hLM (fun _ => x)
    continuous_const (integrable_const ‖x‖)
  have h := (integrable_hasDerivAt_gaussianNoise_of_contDiff_bounded
    (hf.of_le (by norm_num)) hb hm x hr).2
  convert h using 1
  change (∫ y, L y x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) -
    r * ∑ i, ∫ y, fderiv ℝ (fderiv ℝ f) (r • x + s • y) (Pi.single i 1) (Pi.single i 1)
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) =
    ∫ y, L y (x - (r/s) • y) ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)
  simp_rw [map_sub, map_smul, smul_eq_mul]
  change Integrable (fun y => L y y) (Measure.pi fun _ : Fin n => standardGaussianMeasure) at hLy
  change Integrable (fun y => L y x) (Measure.pi fun _ : Fin n => standardGaussianMeasure) at hLx
  rw [integral_sub hLx (hLy.const_mul (r/s)), integral_const_mul,
    integral_fderiv_mehler_apply_self hf hm hk r s x]
  field_simp



/-- Gaussian averaging at correlation `exp(-t)` solves the Ornstein–Uhlenbeck
equation: its time derivative equals the spatial Hessian trace minus the
spatial derivative evaluated on the starting point, for positive t.
[MN15, §2, Ornstein–Uhlenbeck semigroup]

**Proof sketch.** Compose the correlation derivative formula with `exp(-t)`.
Commutation of the first and second spatial derivatives with Gaussian averaging
identifies the gradient and trace terms of the generator. All operator-valued
integrals are integrable by the bounded derivative hypotheses. -/
lemma hasDerivAt_gaussianNoise_exp_neg_generator {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {B M K : ℝ}
    (hb : ∀ z, |f z| ≤ B) (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (hk : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K)
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => gaussianNoise (Real.exp (-u)) f x)
      ((∑ i, fderiv ℝ (fderiv ℝ (gaussianNoise (Real.exp (-t)) f)) x
        (Pi.single i 1) (Pi.single i 1)) -
        fderiv ℝ (gaussianNoise (Real.exp (-t)) f) x x) t := by
  let r := Real.exp (-t)
  let s := Real.sqrt (1-r^2)
  have hr : r ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact lt_trans (by norm_num) (Real.exp_pos _)
    · exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have hDf : Integrable (fun y : Fin n → ℝ => fderiv ℝ f (r • x + s • y))
      (Measure.pi fun _ => standardGaussianMeasure) :=
    Integrable.of_bound
      ((hf.continuous_fderiv (by norm_num)).comp (by fun_prop)).aestronglyMeasurable M
      (Eventually.of_forall fun y => hm _)
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  letI : NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) := inferInstance
  have hH : Integrable (fun y : Fin n → ℝ => fderiv ℝ (fderiv ℝ f) (r • x + s • y))
      (Measure.pi fun _ => standardGaussianMeasure) :=
    Integrable.of_bound
      ((hdf.continuous_fderiv le_rfl).comp (by fun_prop)).aestronglyMeasurable K
      (Eventually.of_forall fun y => hk _)
  have hgrad := (hasFDerivAt_gaussianNoise_of_contDiff_bounded
    (hf.of_le (by norm_num)) hb hm r x).fderiv
  have hhess := (hasFDerivAt_fderiv_gaussianNoise_of_contDiff_bounded hf hb hm hk r x).fderiv
  have hd := (hasDerivAt_gaussianNoise_correlation_generator hf hb hm hk x hr).comp t
    ((hasDerivAt_id t).neg.exp)
  convert hd using 1
  change (∑ i, fderiv ℝ (fderiv ℝ (gaussianNoise r f)) x (Pi.single i 1) (Pi.single i 1)) -
    fderiv ℝ (gaussianNoise r f) x x =
    ((∫ y, fderiv ℝ f (r • x + s • y) x
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) -
      r * ∑ i, ∫ y, fderiv ℝ (fderiv ℝ f) (r • x + s • y) (Pi.single i 1) (Pi.single i 1)
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) * (r * (-1))
  rw [hgrad, hhess]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [ContinuousLinearMap.integral_apply hDf x]
  have hdiag (i : Fin n) :
      ((∫ y, fderiv ℝ (fderiv ℝ f) (r • x + s • y)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) (Pi.single i 1)) (Pi.single i 1) =
      ∫ y, fderiv ℝ (fderiv ℝ f) (r • x + s • y) (Pi.single i 1) (Pi.single i 1)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
    rw [ContinuousLinearMap.integral_apply hH,
      ContinuousLinearMap.integral_apply (hH.apply_continuousLinearMap _) ]
  change (∑ i, r^2 * ((∫ y, fderiv ℝ (fderiv ℝ f) (r • x + s • y)
    ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) (Pi.single i 1)) (Pi.single i 1)) -
    r * (∫ y, fderiv ℝ f (r • x + s • y) x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) = _
  simp_rw [hdiag]
  rw [← Finset.mul_sum]
  ring


end BooleanAnalysis.GaussianSpace
