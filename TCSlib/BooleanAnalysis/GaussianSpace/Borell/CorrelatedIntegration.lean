/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Integration
import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import Mathlib.Analysis.Calculus.Deriv.Pi
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian integration by parts for correlated endpoints

## Main definitions

The existing Gaussian probability law, noise operator, and profile are reused.

## Main results

* `integral_first_coordinate_derivative_gaussianProd`.
* `integral_first_coordinate_derivative_correlatedGaussian`.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/

open MeasureTheory ProbabilityTheory
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
/-- Gaussian integration by parts in a coordinate of the first endpoint of an
independent Gaussian pair.

**Proof sketch.** Apply coordinate integration by parts to almost every
section supplied by Fubini, then integrate the other endpoint. -/
lemma integral_first_coordinate_derivative_gaussianProd {n : ℕ} (i : Fin n)
    (u v : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (hderiv : ∀ x y, HasDerivAt (fun t => u (Function.update x i t, y)) (v (x, y)) (x i))
    (hu : Integrable u ((Measure.pi fun _ => standardGaussianMeasure).prod
      (Measure.pi fun _ => standardGaussianMeasure)))
    (hv : Integrable v ((Measure.pi fun _ => standardGaussianMeasure).prod
      (Measure.pi fun _ => standardGaussianMeasure)))
    (hxu : Integrable (fun z => z.1 i * u z)
      ((Measure.pi fun _ => standardGaussianMeasure).prod
      (Measure.pi fun _ => standardGaussianMeasure))) :
    (∫ z, v z ∂((Measure.pi fun _ => standardGaussianMeasure).prod
      (Measure.pi fun _ => standardGaussianMeasure))) =
    ∫ z, z.1 i * u z ∂((Measure.pi fun _ => standardGaussianMeasure).prod
      (Measure.pi fun _ => standardGaussianMeasure)) := by
  rw [integral_prod_symm _ hv, integral_prod_symm _ hxu]
  apply integral_congr_ae
  filter_upwards [hu.prod_left_ae, hv.prod_left_ae, hxu.prod_left_ae] with y huy hvy hxuy
  exact integral_coordinate_derivative_gaussianPi i (fun x => u (x, y))
    (fun x => v (x, y)) (fun x => hderiv x y) huy hvy hxuy
/-- For a correlated Gaussian pair, integration against its first coordinate
is differentiation in the joint direction `(eᵢ, ρ eᵢ)`.
[MN15, §2, Gaussian integration by parts]

**Proof sketch.** Pull back to independent endpoints. Updating the first
independent coordinate differentiates the two correlated endpoints in directions
`eᵢ` and `ρ eᵢ`. The chain rule and product Gaussian integration by parts give
the identity; transport both integrals through the defining pushforward. -/
lemma integral_first_coordinate_derivative_correlatedGaussian {n : ℕ} (ρ : ℝ) (i : Fin n)
    (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (hH : Differentiable ℝ H)
    (hHint : Integrable H (correlatedGaussianMeasure ρ))
    (hDint : Integrable (fun z => fderiv ℝ H z ((Pi.single i (1 : ℝ) : Fin n → ℝ), ρ • (Pi.single i (1 : ℝ) : Fin n → ℝ)))
      (correlatedGaussianMeasure ρ))
    (hXint : Integrable (fun z => z.1 i * H z) (correlatedGaussianMeasure ρ)) :
    (∫ z, fderiv ℝ H z ((Pi.single i (1 : ℝ) : Fin n → ℝ), ρ • (Pi.single i (1 : ℝ) : Fin n → ℝ))
      ∂correlatedGaussianMeasure ρ) =
    ∫ z, z.1 i * H z ∂correlatedGaussianMeasure ρ := by
  let C := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    (z.1, fun j => ρ * z.1 j + Real.sqrt (1 - ρ ^ 2) * z.2 j)
  have hC : MeasurePreserving C
      ((Measure.pi fun _ => standardGaussianMeasure).prod
        (Measure.pi fun _ => standardGaussianMeasure)) (correlatedGaussianMeasure ρ) :=
    ⟨by fun_prop, rfl⟩
  change (∫ z, fderiv ℝ H z ((Pi.single i (1 : ℝ) : Fin n → ℝ),
      ρ • (Pi.single i (1 : ℝ) : Fin n → ℝ)) ∂Measure.map C
      ((Measure.pi fun _ => standardGaussianMeasure).prod
        (Measure.pi fun _ => standardGaussianMeasure))) =
    ∫ z, z.1 i * H z ∂Measure.map C
      ((Measure.pi fun _ => standardGaussianMeasure).prod
        (Measure.pi fun _ => standardGaussianMeasure))
  rw [integral_map hC.measurable.aemeasurable hDint.aestronglyMeasurable,
    integral_map hC.measurable.aemeasurable hXint.aestronglyMeasurable]
  apply integral_first_coordinate_derivative_gaussianProd i
    (fun z => H (C z)) (fun z => fderiv ℝ H (C z) ((Pi.single i (1 : ℝ) : Fin n → ℝ), ρ • (Pi.single i (1 : ℝ) : Fin n → ℝ)))
    ?_ (hC.integrable_comp_of_integrable hHint)
    (hC.integrable_comp_of_integrable hDint) (hC.integrable_comp_of_integrable hXint)
  intro x y
  have hx : HasDerivAt (fun t => Function.update x i t) ((Pi.single i (1 : ℝ) : Fin n → ℝ)) (x i) :=
    hasDerivAt_update x i (x i)
  have hc : HasDerivAt (fun t => C (Function.update x i t, y))
      ((Pi.single i (1 : ℝ) : Fin n → ℝ), ρ • (Pi.single i (1 : ℝ) : Fin n → ℝ)) (x i) := by
    exact hx.prodMk ((hx.const_smul ρ).add_const
      (fun j => Real.sqrt (1 - ρ ^ 2) * y j))
  simpa only [Function.update_eq_self] using
    (hH (C (Function.update x i (x i), y))).hasFDerivAt.comp_hasDerivAt (x i) hc


end BooleanAnalysis.GaussianSpace
