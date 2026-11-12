/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.ProfileSmoothness
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.CorrelatedIntegration
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Curvature
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.FunctionalDifferentiation
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.ProfileBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The integrated curvature sign in Borell interpolation

## Main definitions

The bivariate profile slopes and correlated Gaussian law are reused.

## Main results

Gaussian integration by parts turns the weighted first-endpoint generator
into minus the averaged curvature. Endpoint exchange gives its sign.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions

/-- The derivative of the first slope times a coordinate derivative of a
function, in the correlated endpoint direction, is the first curvature term
plus the slope-weighted second derivative. [MN15, §2, chain rule calculation]

**Proof sketch.** Use the joint derivative of the slope and the product rule,
then evaluate the resulting linear functional in the correlated direction. -/
lemma fderiv_profileSlope_mul_coordinate {n : ℕ} (ρ : ℝ) (i : Fin n)
    (u du ddu : (Fin n → ℝ) → ℝ) (hu : Differentiable ℝ u)
    (hdu : Differentiable ℝ du) (hrange : ∀ x, u x ∈ Set.Ioo (0 : ℝ) 1)
    (hxu : ∀ x, fderiv ℝ u x ((Pi.single i (1 : ℝ) : Fin n → ℝ)) = du x)
    (hxdu : ∀ x, fderiv ℝ du x ((Pi.single i (1 : ℝ) : Fin n → ℝ)) = ddu x)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    fderiv ℝ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => gaussianBivariateSlope ρ (u z.1) (u z.2) * du z.1) z
      ((Pi.single i (1 : ℝ) : Fin n → ℝ), ρ • (Pi.single i (1 : ℝ) : Fin n → ℝ)) =
      deriv (fun p => gaussianBivariateSlope ρ p (u z.2)) (u z.1) * (du z.1) ^ 2 +
        ρ * deriv (fun p => gaussianBivariateSlope ρ (u z.1) p) (u z.2) *
          du z.1 * du z.2 +
        gaussianBivariateSlope ρ (u z.1) (u z.2) * ddu z.1 := by
  have hu1 := (hu z.1).hasFDerivAt.comp z hasFDerivAt_fst
  have hu2 := (hu z.2).hasFDerivAt.comp z hasFDerivAt_snd
  have hs := (hasFDerivAt_gaussianBivariateSlope ρ (hrange z.1) (hrange z.2)).comp z
    (hu1.prodMk hu2)
  have hprod := hs.mul ((hdu z.1).hasFDerivAt.comp z hasFDerivAt_fst)
  dsimp only [Function.comp_def, Pi.mul_apply] at hprod
  have hf := hprod.fderiv
  change fderiv ℝ (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    gaussianBivariateSlope ρ (u z.1) (u z.2) * du z.1) z = _ at hf
  rw [hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    map_smul, smul_eq_mul]
  change gaussianBivariateSlope ρ (u z.1) (u z.2) *
      fderiv ℝ du z.1 ((Pi.single i (1 : ℝ) : Fin n → ℝ)) +
    du z.1 * (deriv (fun p => gaussianBivariateSlope ρ p (u z.2)) (u z.1) *
      fderiv ℝ u z.1 ((Pi.single i (1 : ℝ) : Fin n → ℝ)) +
    deriv (fun p => gaussianBivariateSlope ρ (u z.1) p) (u z.2) *
      (ρ * fderiv ℝ u z.2 ((Pi.single i (1 : ℝ) : Fin n → ℝ)))) = _
  rw [hxu, hxu, hxdu]
  ring


/-- The integral of the slope-weighted first-endpoint coordinate generator
is minus the corresponding curvature integral, under explicit integrability
hypotheses. [MN15, §2, Gaussian integration by parts]

**Proof sketch.** Differentiate the slope times the coordinate derivative.
Correlated Gaussian integration by parts replaces this derivative by the
coordinate-weighted product. Subtract the second-derivative term and rearrange. -/
lemma integral_profileSlope_generator_first {n : ℕ} (ρ : ℝ) (i : Fin n)
    (u du ddu : (Fin n → ℝ) → ℝ) (hu : Differentiable ℝ u)
    (hdu : Differentiable ℝ du) (hrange : ∀ x, u x ∈ Set.Ioo (0 : ℝ) 1)
    (hxu : ∀ x, fderiv ℝ u x (Pi.single i 1) = du x)
    (hxdu : ∀ x, fderiv ℝ du x (Pi.single i 1) = ddu x)
    (hH : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      gaussianBivariateSlope ρ (u z.1) (u z.2) * du z.1) (correlatedGaussianMeasure ρ))
    (hL : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      gaussianBivariateSlope ρ (u z.1) (u z.2) * ddu z.1) (correlatedGaussianMeasure ρ))
    (hX : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      z.1 i * (gaussianBivariateSlope ρ (u z.1) (u z.2) * du z.1))
      (correlatedGaussianMeasure ρ))
    (hC : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      deriv (fun p => gaussianBivariateSlope ρ p (u z.2)) (u z.1) * (du z.1) ^ 2 +
        ρ * deriv (fun p => gaussianBivariateSlope ρ (u z.1) p) (u z.2) *
          du z.1 * du z.2) (correlatedGaussianMeasure ρ)) :
    (∫ z, gaussianBivariateSlope ρ (u z.1) (u z.2) *
      (ddu z.1 - z.1 i * du z.1) ∂correlatedGaussianMeasure ρ) =
    -(∫ z, deriv (fun p => gaussianBivariateSlope ρ p (u z.2)) (u z.1) * (du z.1) ^ 2 +
        ρ * deriv (fun p => gaussianBivariateSlope ρ (u z.1) p) (u z.2) *
          du z.1 * du z.2 ∂correlatedGaussianMeasure ρ) := by
  have hdiff : Differentiable ℝ (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      gaussianBivariateSlope ρ (u z.1) (u z.2) * du z.1) := by
    intro z
    exact ((differentiableAt_gaussianBivariateSlope ρ ⟨hrange z.1, hrange z.2⟩).comp z
      (((hu z.1).comp z differentiableAt_fst).prodMk
        ((hu z.2).comp z differentiableAt_snd))).mul
      ((hdu z.1).comp z differentiableAt_fst)
  have heq := integral_first_coordinate_derivative_correlatedGaussian ρ i _
    hdiff hH ((hC.add hL).congr (Filter.Eventually.of_forall (fun z =>
      (fderiv_profileSlope_mul_coordinate ρ i u du ddu hu hdu hrange hxu hxdu z).symm))) hX
  have heq' : (∫ z, deriv (fun p => gaussianBivariateSlope ρ p (u z.2)) (u z.1) *
        (du z.1) ^ 2 + ρ * deriv (fun p => gaussianBivariateSlope ρ (u z.1) p) (u z.2) *
        du z.1 * du z.2 ∂correlatedGaussianMeasure ρ) +
      (∫ z, gaussianBivariateSlope ρ (u z.1) (u z.2) * ddu z.1
        ∂correlatedGaussianMeasure ρ) =
      ∫ z, z.1 i * (gaussianBivariateSlope ρ (u z.1) (u z.2) * du z.1)
        ∂correlatedGaussianMeasure ρ := by
    rw [← integral_add hC hL, ← heq]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z =>
      (fderiv_profileSlope_mul_coordinate ρ i u du ddu hu hdu hrange hxu hxdu z).symm))
  calc
    _ = (∫ z, gaussianBivariateSlope ρ (u z.1) (u z.2) * ddu z.1
          ∂correlatedGaussianMeasure ρ) -
        ∫ z, z.1 i * (gaussianBivariateSlope ρ (u z.1) (u z.2) * du z.1)
          ∂correlatedGaussianMeasure ρ := by
      rw [← integral_sub hL hX]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by ring)
    _ = _ := by linarith


/-- The first-endpoint curvature contribution has nonpositive Gaussian
expectation for positive correlation and interior function values.
[MN15, §2, sign of the interpolation derivative]

**Proof sketch.** Endpoint exchange preserves the correlated Gaussian law,
so the curvature integral equals its exchanged version. Adding them gives
the full correlation-weighted quadratic, which is pointwise nonpositive. -/
lemma integral_profileSlope_curvature_nonpos {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (u du : (Fin n → ℝ) → ℝ)
    (hrange : ∀ x, u x ∈ Set.Ioo (0 : ℝ) 1)
    (hC : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      deriv (fun p => gaussianBivariateSlope ρ p (u z.2)) (u z.1) * (du z.1) ^ 2 +
        ρ * deriv (fun p => gaussianBivariateSlope ρ (u z.1) p) (u z.2) *
          du z.1 * du z.2) (correlatedGaussianMeasure ρ)) :
    (∫ z, deriv (fun p => gaussianBivariateSlope ρ p (u z.2)) (u z.1) * (du z.1) ^ 2 +
        ρ * deriv (fun p => gaussianBivariateSlope ρ (u z.1) p) (u z.2) *
          du z.1 * du z.2 ∂correlatedGaussianMeasure ρ) ≤ 0 := by
  let C : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun z =>
    deriv (fun p => gaussianBivariateSlope ρ p (u z.2)) (u z.1) * (du z.1) ^ 2 +
      ρ * deriv (fun p => gaussianBivariateSlope ρ (u z.1) p) (u z.2) *
        du z.1 * du z.2
  have hc : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2.le⟩
  have hp : MeasurePreserving (Prod.swap :
      ((Fin n → ℝ) × (Fin n → ℝ)) → ((Fin n → ℝ) × (Fin n → ℝ)))
      (correlatedGaussianMeasure ρ) (correlatedGaussianMeasure ρ) :=
    ⟨measurable_swap, correlatedGaussianMeasure_swap hc⟩
  have hi := hp.integrable_comp_of_integrable hC
  have heq : (∫ z, C z.swap ∂correlatedGaussianMeasure ρ) =
      ∫ z, C z ∂correlatedGaussianMeasure ρ := by
    exact hp.integral_comp (MeasurableEquiv.prodComm.measurableEmbedding) C
  have hnonpos : (∫ z, C z + C z.swap ∂correlatedGaussianMeasure ρ) ≤ 0 := by
    apply integral_nonpos_of_ae
    apply Filter.Eventually.of_forall
    intro z
    have hm := gaussianBivariateSlope_mixed_deriv_symm
      (show ρ ∈ Set.Ioo (-1 : ℝ) 1 from ⟨by linarith [hρ.1], hρ.2⟩)
      (hrange z.1) (hrange z.2)
    have hq := gaussianBivariate_curvature_nonpos hρ (hrange z.1) (hrange z.2)
      (du z.1) (du z.2)
    dsimp [C]
    dsimp only [Prod.swap] at *
    rw [← hm]
    nlinarith only [hq]
  have hC' : Integrable C (correlatedGaussianMeasure ρ) := hC
  have hi' : Integrable (fun z => C z.swap) (correlatedGaussianMeasure ρ) := hi
  rw [integral_add hC' hi', heq] at hnonpos
  change (∫ z, C z ∂correlatedGaussianMeasure ρ) ≤ 0
  linarith only [hnonpos]


end BooleanAnalysis.GaussianSpace
