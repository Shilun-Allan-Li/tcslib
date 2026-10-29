/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.ThresholdFunctions.GaussianTail
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian integration by parts under explicit integrability hypotheses

## Main definitions

The existing one-dimensional standard Gaussian measure and density are reused.

## Main results

* `integrable_standardGaussianPDF_mul`: convert Gaussian to density-weighted integrability.
* `integral_derivative_standardGaussian`: the scalar Gaussian integration-by-parts identity.
* `integral_coordinate_derivative_gaussianPi`: its finite-product coordinate version.

This generalizes the polynomial argument in `Hermite.Orthogonality` to
differentiable functions, as needed by the Borell interpolation.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian integration by parts;
  §11.2, proof of Proposition 11.30.
* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2, equation (2.1).
-/

open MeasureTheory ProbabilityTheory

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- A Gaussian integrable function becomes Lebesgue integrable after
multiplication by the standard Gaussian density. -/
lemma integrable_standardGaussianPDF_mul {u : ℝ → ℝ}
    (hu : Integrable u standardGaussianMeasure) :
    Integrable (fun x => standardGaussianPDF x * u x) := by
  rw [standardGaussianMeasure, gaussianReal_of_var_ne_zero 0 one_ne_zero] at hu
  simpa only [toReal_gaussianPDF, smul_eq_mul, standardGaussianPDF] using
    (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)).mp hu

/-- The Gaussian mean of a derivative equals the mean of the original function
multiplied by its coordinate, when both functions and the coordinate product
are integrable. [OD14, §11.1, Gaussian integration by parts; MN15, equation (2.1)]
This extends the polynomial identity to arbitrary differentiable functions under
explicit integrability hypotheses.

**Proof sketch.** Multiply the function by the Gaussian density and differentiate.
The product and its derivative are Lebesgue integrable, so the derivative has
integral zero. Rearranging gives the claimed identity. -/
lemma integral_derivative_standardGaussian (u u' : ℝ → ℝ)
    (hderiv : ∀ x, HasDerivAt u (u' x) x)
    (hu : Integrable u standardGaussianMeasure)
    (hu' : Integrable u' standardGaussianMeasure)
    (hxu : Integrable (fun x => x * u x) standardGaussianMeasure) :
    (∫ x, u' x ∂standardGaussianMeasure) =
      ∫ x, x * u x ∂standardGaussianMeasure := by
  have hweighted := integrable_standardGaussianPDF_mul hu
  have hweighted' := integrable_standardGaussianPDF_mul hu'
  have hxweighted := integrable_standardGaussianPDF_mul hxu
  have hzero : (∫ x, standardGaussianPDF x * u' x -
      standardGaussianPDF x * (x * u x)) = 0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun x => standardGaussianPDF x * u x)
    · intro x
      convert (hasDerivAt_standardGaussianPDF x).mul (hderiv x) using 1
      ring
    · exact hweighted'.sub hxweighted
    · exact hweighted
  rw [integral_sub hweighted' hxweighted] at hzero
  simpa only [standardGaussianMeasure,
    integral_gaussianReal_eq_integral_smul one_ne_zero,
    smul_eq_mul, standardGaussianPDF] using sub_eq_zero.mp hzero

/-- The Gaussian mean of a coordinate derivative equals the mean of the
function multiplied by that coordinate, under explicit integrability
hypotheses. [OD14, §11.1, Gaussian integration by parts; MN15, equation (2.1)]

**Proof sketch.** Separate the chosen coordinate from the remaining coordinates
using the measure-preserving finite-product equivalence. Fubini supplies
integrable sections almost everywhere. Apply scalar Gaussian integration by
parts to each section, then integrate over the remaining coordinates. -/
lemma integral_coordinate_derivative_gaussianPi {n : ℕ} (i : Fin n)
    (u v : (Fin n → ℝ) → ℝ)
    (hderiv : ∀ x, HasDerivAt (fun t => u (Function.update x i t)) (v x) (x i))
    (hu : Integrable u (Measure.pi fun _ => standardGaussianMeasure))
    (hv : Integrable v (Measure.pi fun _ => standardGaussianMeasure))
    (hxu : Integrable (fun x => x i * u x)
      (Measure.pi fun _ => standardGaussianMeasure)) :
    (∫ x, v x ∂(Measure.pi fun _ => standardGaussianMeasure)) =
      ∫ x, x i * u x ∂(Measure.pi fun _ => standardGaussianMeasure) := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
    have he := (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => standardGaussianMeasure) i).symm e
    have huE := he.integrable_comp_of_integrable hu
    have hvE := he.integrable_comp_of_integrable hv
    have hxuE := he.integrable_comp_of_integrable hxu
    simp only [Function.comp_def] at huE hvE hxuE
    rw [← he.integral_comp' v, ← he.integral_comp' (fun x => x i * u x),
      integral_prod_symm _ hvE, integral_prod_symm _ hxuE]
    apply integral_congr_ae
    filter_upwards [huE.prod_left_ae, hvE.prod_left_ae, hxuE.prod_left_ae] with
      x hux hvx hxux
    have hei : ∀ t, e.symm (t, x) i = t := by
      intro t
      simp [e]
    simp_rw [hei] at hxux ⊢
    refine integral_derivative_standardGaussian (fun t => u (e.symm (t, x)))
      (fun t => v (e.symm (t, x))) ?_ hux hvx hxux
    intro t
    simpa [e, Fin.insertNthEquiv, Fin.update_insertNth] using hderiv (e.symm (t, x))

/-- Integrating on a Gaussian lower half-line equals the corresponding
Lebesgue integral weighted by the standard Gaussian density. -/
lemma integral_Iic_standardGaussianMeasure (f : ℝ → ℝ) (t : ℝ) :
    (∫ x in Set.Iic t, f x ∂standardGaussianMeasure) =
      ∫ x in Set.Iic t, standardGaussianPDF x * f x := by
  rw [← integral_indicator measurableSet_Iic, standardGaussianMeasure,
    integral_gaussianReal_eq_integral_smul one_ne_zero,
    ← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ≤ t <;> simp [Set.indicator, hx, smul_eq_mul, standardGaussianPDF]

end BooleanAnalysis.GaussianSpace
