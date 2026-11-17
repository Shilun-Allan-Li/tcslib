/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Fourier
import Mathlib.Analysis.Calculus.ParametricIntegral
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Differentiating the Mehler integral in its correlation

## Main definitions

The Gaussian noise operator is reused.

## Main results

* `integrable_hasDerivAt_gaussianNoise_of_contDiff_bounded`: the correlation
  derivative of Gaussian noise for bounded C1 functions with bounded derivative.

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
/-- The correlated Gaussian endpoint has derivative
`x - r / sqrt (1-r²) • y` at every interior correlation. -/
lemma hasDerivAt_gaussianMehlerCurve {n : ℕ} (x y : Fin n → ℝ) {r : ℝ}
    (hr : r ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun q : ℝ => fun i => q * x i + Real.sqrt (1 - q ^ 2) * y i)
      (fun i => x i - r / Real.sqrt (1 - r ^ 2) * y i) r := by
  have hpos : 0 < 1 - r ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hr.2) (sub_pos.mpr hr.1)]
  have hs : HasDerivAt (fun q : ℝ => Real.sqrt (1 - q ^ 2))
      (-r / Real.sqrt (1 - r ^ 2)) r := by
    convert (((hasDerivAt_id r).pow 2).const_sub 1).sqrt hpos.ne' using 1
    simp
    field_simp
  convert ((hasDerivAt_id r).smul_const x).add (hs.smul_const y) using 1
  ext i
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
/-- The coefficient `q / sqrt (1-q²)` is locally bounded at interior correlations. -/
private lemma gaussianMehlerCoefficient_locally_bounded {r : ℝ}
    (hr : r ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ δ > 0, ∀ q ∈ Metric.ball r δ, q ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |q / Real.sqrt (1 - q ^ 2)| ≤ |r / Real.sqrt (1 - r ^ 2)| + 1 := by
  have hpos : 0 < 1 - r ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hr.2) (sub_pos.mpr hr.1)]
  have hc0 : ContinuousAt (fun q : ℝ => q / Real.sqrt (1 - q ^ 2)) r := by
    apply ContinuousAt.div
    · exact continuousAt_id
    · fun_prop
    · exact (Real.sqrt_pos.mpr hpos).ne'
  have hc := hc0.abs
  apply Metric.eventually_nhds_iff_ball.mp
  filter_upwards [isOpen_Ioo.mem_nhds hr,
    hc.eventually (gt_mem_nhds (lt_add_one |r / Real.sqrt (1 - r ^ 2)|))] with q hq hbound
  exact ⟨hq, hbound.le⟩
/-- For a bounded C1 function with bounded derivative, the correlation derivative
of its Gaussian noise average is the integral of the derivative along the
Mehler endpoint. [MN15, §2, differentiation of the Ornstein–Uhlenbeck average]

**Proof sketch.** On a neighborhood of an interior correlation, the coefficient
of the Gaussian integration variable in the endpoint derivative is uniformly
bounded. The chain rule therefore bounds the differentiated integrand by a
constant times one plus the Gaussian vector norm. This bound is integrable,
so differentiation under the integral applies. -/
lemma integrable_hasDerivAt_gaussianNoise_of_contDiff_bounded {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {B M : ℝ}
    (hfbound : ∀ z, |f z| ≤ B) (hdfbound : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (x : Fin n → ℝ) {r : ℝ} (hr : r ∈ Set.Ioo (-1 : ℝ) 1) :
    Integrable (fun y => fderiv ℝ f (fun i => r * x i + Real.sqrt (1 - r ^ 2) * y i)
      (fun i => x i - r / Real.sqrt (1 - r ^ 2) * y i))
      (Measure.pi fun _ => standardGaussianMeasure) ∧
    HasDerivAt (fun q => gaussianNoise q f x)
      (∫ y, fderiv ℝ f (fun i => r * x i + Real.sqrt (1 - r ^ 2) * y i)
        (fun i => x i - r / Real.sqrt (1 - r ^ 2) * y i)
        ∂(Measure.pi fun _ => standardGaussianMeasure)) r := by
  let F : ℝ → (Fin n → ℝ) → ℝ := fun q y =>
    f (fun i => q * x i + Real.sqrt (1 - q ^ 2) * y i)
  let F' : ℝ → (Fin n → ℝ) → ℝ := fun q y =>
    fderiv ℝ f (fun i => q * x i + Real.sqrt (1 - q ^ 2) * y i)
      (fun i => x i - q / Real.sqrt (1 - q ^ 2) * y i)
  obtain ⟨δ, hδ, hlocal⟩ := gaussianMehlerCoefficient_locally_bounded hr
  have hM : 0 ≤ M := (norm_nonneg (fderiv ℝ f 0)).trans (hdfbound 0)
  have hFcont (q) : Continuous (F q) := hf.continuous.comp (by fun_prop)
  have hF'cont : Continuous (F' r) := by
    exact ((hf.continuous_fderiv le_rfl).comp
      (show Continuous (fun y : Fin n → ℝ => fun i =>
        r * x i + Real.sqrt (1 - r ^ 2) * y i) by fun_prop)).clm_apply (by fun_prop)
  have hFint : Integrable (F r) (Measure.pi fun _ => standardGaussianMeasure) :=
    Integrable.of_bound (hFcont r).aestronglyMeasurable B
      (Eventually.of_forall fun y => by
        simpa only [F, Real.norm_eq_abs] using hfbound
          (fun i => r * x i + Real.sqrt (1 - r ^ 2) * y i))
  have hbound (y : Fin n → ℝ) (q : ℝ) (hq : q ∈ Metric.ball r δ) :
      ‖F' q y‖ ≤ M * (‖x‖ + (|r / Real.sqrt (1 - r ^ 2)| + 1) * ‖y‖) := by
    calc
      _ ≤ M * ‖fun i => x i - q / Real.sqrt (1 - q ^ 2) * y i‖ :=
        ((fderiv ℝ f _).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hdfbound _) (norm_nonneg _))
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hM
        change ‖x - (q / Real.sqrt (1 - q ^ 2)) • y‖ ≤ _
        calc
          _ ≤ ‖x‖ + ‖(q / Real.sqrt (1 - q ^ 2)) • y‖ := norm_sub_le _ _
          _ = ‖x‖ + |q / Real.sqrt (1 - q ^ 2)| * ‖y‖ := by
            rw [norm_smul, Real.norm_eq_abs]
          _ ≤ _ := add_le_add_left
            (mul_le_mul_of_nonneg_right (hlocal q hq).2 (norm_nonneg y)) _
  have hnorm : Integrable (fun y : Fin n → ℝ => ‖y‖)
      (Measure.pi fun _ => standardGaussianMeasure) := by
    simpa only [pow_one] using (integrable_gaussianPi_norm_pow (n := n) 1)
  have hboundint : Integrable
      (fun y : Fin n → ℝ => M * (‖x‖ + (|r / Real.sqrt (1 - r ^ 2)| + 1) * ‖y‖))
      (Measure.pi fun _ => standardGaussianMeasure) :=
    ((integrable_const ‖x‖).add (hnorm.const_mul _)).const_mul M
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') hδ
    (Eventually.of_forall fun q => (hFcont q).aestronglyMeasurable)
    hFint hF'cont.aestronglyMeasurable
    (Eventually.of_forall fun y q hq => hbound y q hq) hboundint
    (Eventually.of_forall fun y q hq =>
      (hf.differentiable le_rfl _).hasFDerivAt.comp_hasDerivAt q
        (hasDerivAt_gaussianMehlerCurve x y (hlocal q hq).1))
/-- The correlation derivative of Gaussian noise has at most linear growth
in the starting-point norm, uniformly on compact interior correlation intervals.
[MN15, §2, differentiation under the integral]

**Proof sketch.** Bound the differentiated integrand by the derivative bound
times the endpoint velocity norm. The triangle inequality separates the
starting-point norm from the finite first Gaussian norm moment. -/
lemma abs_deriv_gaussianNoise_correlation_le {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {B M : ℝ}
    (hfbound : ∀ z, |f z| ≤ B) (hdfbound : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (x : Fin n → ℝ) {r : ℝ} (hr : r ∈ Set.Ioo (-1 : ℝ) 1) :
    |deriv (fun q => gaussianNoise q f x) r| ≤
      M * (‖x‖ + |r / Real.sqrt (1 - r ^ 2)| *
        ∫ y : Fin n → ℝ, ‖y‖ ∂(Measure.pi fun _ => standardGaussianMeasure)) := by
  have hM : 0 ≤ M := (norm_nonneg (fderiv ℝ f 0)).trans (hdfbound 0)
  have hnorm : Integrable (fun y : Fin n → ℝ => ‖y‖)
      (Measure.pi fun _ => standardGaussianMeasure) := by
    simpa only [pow_one] using (integrable_gaussianPi_norm_pow (n := n) 1)
  have hbint : Integrable (fun y : Fin n → ℝ =>
      M * (‖x‖ + |r / Real.sqrt (1 - r ^ 2)| * ‖y‖))
      (Measure.pi fun _ => standardGaussianMeasure) :=
    ((integrable_const ‖x‖).add (hnorm.const_mul _)).const_mul M
  rw [(integrable_hasDerivAt_gaussianNoise_of_contDiff_bounded hf hfbound hdfbound x hr).2.deriv]
  have hh := norm_integral_le_of_norm_le hbint (Eventually.of_forall fun y => show
      ‖fderiv ℝ f (fun i => r * x i + Real.sqrt (1 - r ^ 2) * y i)
        (fun i => x i - r / Real.sqrt (1 - r ^ 2) * y i)‖ ≤
        M * (‖x‖ + |r / Real.sqrt (1 - r ^ 2)| * ‖y‖) from by
    calc
      _ ≤ M * ‖x - (r / Real.sqrt (1 - r ^ 2)) • y‖ :=
        ((fderiv ℝ f _).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hdfbound _) (norm_nonneg _))
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        simpa only [norm_smul, Real.norm_eq_abs] using
          norm_sub_le x ((r / Real.sqrt (1 - r ^ 2)) • y)) hM)
  simpa only [Real.norm_eq_abs, integral_const_mul,
    integral_add (integrable_const ‖x‖) (hnorm.const_mul _), integral_const,
    measureReal_univ_eq_one, one_smul] using hh

end BooleanAnalysis.GaussianSpace
