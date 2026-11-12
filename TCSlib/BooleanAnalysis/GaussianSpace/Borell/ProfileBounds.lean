/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.ProfileCalculus

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bounds for derivatives of the Gaussian profile away from endpoint volumes

## Main definitions

The conditional Gaussian cdf slope is reused.

## Main results

On every compact interior probability square the scalar derivatives of the
conditional cdf slope are uniformly bounded.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/

open MeasureTheory Filter
open scoped Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions

/-- Both partial derivatives of the conditional Gaussian cdf slope are bounded
on every closed probability square separated from zero and one.
[MN15, §2, clipped-function derivative bounds]

**Proof sketch.** The explicit derivative formulas are continuous on the
interior probability square: Gaussian quantiles are differentiable there and
the marginal Gaussian densities never vanish. Their absolute values therefore
have finite upper bounds on its compact sub-square. -/
lemma gaussianBivariateSlope_derivatives_bounded (ρ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ C : ℝ, ∀ a ∈ Set.Icc δ (1 - δ), ∀ b ∈ Set.Icc δ (1 - δ),
      |deriv (fun p => gaussianBivariateSlope ρ p b) a| ≤ C ∧
      |deriv (fun p => gaussianBivariateSlope ρ a p) b| ≤ C := by
  let s := Real.sqrt (1 - ρ ^ 2)
  let A (p : ℝ × ℝ) := -ρ * standardGaussianPDF
    ((standardGaussianQuantile p.2 - ρ * standardGaussianQuantile p.1) / s) /
      (s * gaussianIsoperimetric p.1)
  let B (p : ℝ × ℝ) := standardGaussianPDF
    ((standardGaussianQuantile p.2 - ρ * standardGaussianQuantile p.1) / s) /
      (s * gaussianIsoperimetric p.2)
  let K := Set.Icc δ (1 - δ) ×ˢ Set.Icc δ (1 - δ)
  have hmem {a : ℝ} (ha : a ∈ Set.Icc δ (1 - δ)) : a ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hδ.trans_le ha.1, by linarith [ha.2]⟩
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr (by nlinarith [hρ.1, hρ.2])).ne'
  have hc (p : ℝ × ℝ) (hp : p ∈ K) : ContinuousAt A p ∧ ContinuousAt B p := by
    have hq₁ : ContinuousAt (fun z : ℝ × ℝ => standardGaussianQuantile z.1) p :=
      (hasDerivAt_standardGaussianQuantile (hmem hp.1)).continuousAt.comp continuousAt_fst
    have hq₂ : ContinuousAt (fun z : ℝ × ℝ => standardGaussianQuantile z.2) p :=
      (hasDerivAt_standardGaussianQuantile (hmem hp.2)).continuousAt.comp continuousAt_snd
    have hU₁ : ContinuousAt (fun z : ℝ × ℝ => gaussianIsoperimetric z.1) p :=
      (hasDerivAt_gaussianIsoperimetric (hmem hp.1)).continuousAt.comp continuousAt_fst
    have hU₂ : ContinuousAt (fun z : ℝ × ℝ => gaussianIsoperimetric z.2) p :=
      (hasDerivAt_gaussianIsoperimetric (hmem hp.2)).continuousAt.comp continuousAt_snd
    have hpdf : ContinuousAt (fun z : ℝ × ℝ => standardGaussianPDF
        ((standardGaussianQuantile z.2 - ρ * standardGaussianQuantile z.1) / s)) p :=
      continuous_standardGaussianPDF.continuousAt.comp ((hq₂.sub (hq₁.const_mul ρ)).div_const s)
    exact ⟨(hpdf.const_mul (-ρ)).div (hU₁.const_mul s)
      (mul_ne_zero hs (standardGaussianPDF_pos _).ne'),
      hpdf.div (hU₂.const_mul s) (mul_ne_zero hs (standardGaussianPDF_pos _).ne')⟩
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨CA, hCA⟩ := hK.bddAbove_image
    (show ContinuousOn (fun p => |A p|) K from fun p hp =>
      ((hc p hp).1.abs).continuousWithinAt)
  obtain ⟨CB, hCB⟩ := hK.bddAbove_image
    (show ContinuousOn (fun p => |B p|) K from fun p hp =>
      ((hc p hp).2.abs).continuousWithinAt)
  refine ⟨max CA CB, fun a ha b hb => ?_⟩
  have hA : |A (a,b)| ≤ CA := hCA (Set.mem_image_of_mem _ ⟨ha,hb⟩)
  have hB : |B (a,b)| ≤ CB := hCB (Set.mem_image_of_mem _ ⟨ha,hb⟩)
  constructor
  · exact (show |deriv (fun p => gaussianBivariateSlope ρ p b) a| = |A (a,b)| by
      exact congrArg abs (hasDerivAt_gaussianBivariateSlope_left ρ b (hmem ha)).deriv).le.trans
        (hA.trans (le_max_left _ _))
  · exact (show |deriv (fun p => gaussianBivariateSlope ρ a p) b| = |B (a,b)| by
      exact congrArg abs (hasDerivAt_gaussianBivariateSlope_right ρ a (hmem hb)).deriv).le.trans
        (hB.trans (le_max_right _ _))

/-- The two partial derivatives of the conditional cdf slope, composed with
continuous interior-volume functions, are continuous.
[MN15, §2, profile derivative formulas]

**Proof sketch.** Substitute the explicit Gaussian density formulas. The
quantiles and marginal densities are continuous at interior volumes and the
density denominators do not vanish. -/

lemma continuous_gaussianBivariateSlope_deriv_comp {E : Type*} [TopologicalSpace E]
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (u v : E → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hurange : ∀ x, u x ∈ Set.Ioo (0 : ℝ) 1)
    (hvrange : ∀ x, v x ∈ Set.Ioo (0 : ℝ) 1) :
    Continuous (fun x => deriv (fun p => gaussianBivariateSlope ρ p (v x)) (u x)) ∧
    Continuous (fun x => deriv (fun p => gaussianBivariateSlope ρ (u x) p) (v x)) := by
  let s := Real.sqrt (1 - ρ ^ 2)
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr (by nlinarith [hρ.1,hρ.2])).ne'
  have hqu : Continuous (fun x => standardGaussianQuantile (u x)) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (hasDerivAt_standardGaussianQuantile (hurange x)).continuousAt.comp (hu.continuousAt))
  have hqv : Continuous (fun x => standardGaussianQuantile (v x)) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (hasDerivAt_standardGaussianQuantile (hvrange x)).continuousAt.comp (hv.continuousAt))
  have hUu : Continuous (fun x => gaussianIsoperimetric (u x)) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (hasDerivAt_gaussianIsoperimetric (hurange x)).continuousAt.comp (hu.continuousAt))
  have hUv : Continuous (fun x => gaussianIsoperimetric (v x)) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (hasDerivAt_gaussianIsoperimetric (hvrange x)).continuousAt.comp (hv.continuousAt))
  have hpdf : Continuous (fun x => standardGaussianPDF
      ((standardGaussianQuantile (v x) - ρ * standardGaussianQuantile (u x)) / s)) :=
    continuous_standardGaussianPDF.comp ((hqv.sub (continuous_const.mul hqu)).div_const s)
  constructor
  · have hA := ((continuous_const (y := -ρ)).mul hpdf).div (continuous_const.mul hUu)
      (fun x => mul_ne_zero hs (standardGaussianPDF_pos _).ne')
    convert hA using 1
    funext x
    exact (hasDerivAt_gaussianBivariateSlope_left ρ (v x) (hurange x)).deriv
  · have hB := hpdf.div (continuous_const.mul hUv)
      (fun x => mul_ne_zero hs (standardGaussianPDF_pos _).ne')
    convert hB using 1
    funext x
    exact (hasDerivAt_gaussianBivariateSlope_right ρ (u x) (hvrange x)).deriv


end BooleanAnalysis.GaussianSpace
