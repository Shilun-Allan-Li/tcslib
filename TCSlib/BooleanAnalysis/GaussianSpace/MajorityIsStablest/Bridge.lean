/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.InputMoments
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Moments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Boolean and Gaussian multilinear stability

## Main definitions

The existing multilinear Fourier extension is used without a new representation.

## Main results

Gaussian extension preserves the mean, second moment, and noise stability.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.7, proof of (11.39).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace.MajorityIsStablest

open ThresholdFunctions Hypercontractivity

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  hasInvarianceMoments_standardGaussian.reasonable.probability

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

/-- A multilinear Gaussian extension is measurable. -/
lemma gaussianExtension_measurable (f : BooleanFunc n) :
    Measurable (evalMultilinearRV (fourierCoeff f) (fun i (z : Fin n → ℝ) => z i)) := by
  unfold evalMultilinearRV
  fun_prop

/-- Independent Gaussian coordinates have the product Gaussian law. -/
lemma gaussianCoordinates_independent :
    iIndepFun (fun (i : Fin n) (z : Fin n → ℝ) => z i) γ :=
  iIndepFun_pi (μ := fun _ : Fin n => standardGaussianMeasure)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)

/-- A multilinear Gaussian extension has finite second moment. [OD14, §11.6] -/
lemma gaussianExtension_memLp (f : BooleanFunc n) :
    MemLp (evalMultilinearRV (fourierCoeff f) (fun i z => z i)) 2 γ := by
  exact (evalMultilinearRV_memLp _ _ _ gaussianCoordinates_independent
    (fun i => (hasInvarianceMoments_gaussianCoordinate i).reasonable.memLp)).mono_exponent
      (by norm_num)

/-- Gaussian extension preserves the Boolean mean. [OD14, Remark 11.64] -/
lemma integral_gaussianExtension (f : BooleanFunc n) :
    (∫ z, evalMultilinearRV (fourierCoeff f) (fun i z => z i) z ∂γ) = expect f := by
  rw [MultilinearMoments.integral_eval _ _ gaussianCoordinates_independent
    (fun i => (hasInvarianceMoments_gaussianCoordinate i).reasonable.memLp)
    (fun i => (hasInvarianceMoments_gaussianCoordinate i).mean)
    (fun i => (hasInvarianceMoments_gaussianCoordinate i).second), fourierCoeff_empty]

/-- Gaussian extension preserves the Boolean second moment. [OD14, Remark 11.64] -/
lemma integral_gaussianExtension_sq (f : BooleanFunc n) :
    (∫ z, evalMultilinearRV (fourierCoeff f) (fun i z => z i) z ^ 2 ∂γ) =
      expect (fun x => f x ^ 2) := by
  rw [MultilinearMoments.integral_eval_sq _ _ gaussianCoordinates_independent
    (fun i => (hasInvarianceMoments_gaussianCoordinate i).reasonable.memLp)
    (fun i => (hasInvarianceMoments_gaussianCoordinate i).mean)
    (fun i => (hasInvarianceMoments_gaussianCoordinate i).second)]
  simpa only [innerProduct, pow_two] using (parseval f).symm

/-- Gaussian extensions of unit-interval-valued functions have L² norm at most one.
[OD14, §11.7, proof of (11.39)] -/
lemma gaussianExtension_two_norm_le_one (f : BooleanFunc n)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    rvLpNorm (evalMultilinearRV (fourierCoeff f) (fun i z => z i)) γ 2 ≤ 1 := by
  have hsq := rvLpNorm_rpow
    (evalMultilinearRV (fourierCoeff f) (fun i z => z i)) γ 2 (by norm_num)
    (by simpa only [ENNReal.ofReal_ofNat] using gaussianExtension_memLp f)
  simp only [Real.rpow_two, sq_abs, integral_gaussianExtension_sq] at hsq
  have he : expect (fun x => f x ^ 2) ≤ 1 := by
    calc
      _ ≤ expect (fun _ : BoolCube n => (1 : ℝ)) := expect_mono fun x => by
        have hx := hf x
        nlinarith [hx.1, hx.2]
      _ = 1 := expect_const 1
  nlinarith

/-- The Gaussian stability of the multilinear extension equals Boolean stability.
[OD14, §11.7, proof of (11.39)]

**Proof sketch.** Gaussian averaging multiplies each multilinear coefficient by
correlation to its degree, just as Boolean noise does. Matching mixed polynomial
moments and Boolean Plancherel then identify the two stabilities. -/
theorem gaussianNoiseStability_fourier_extension (f : BooleanFunc n) {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    gaussianNoiseStability ρ (evalMultilinearRV (fourierCoeff f) (fun i z => z i)) =
      noiseStability ρ f := by
  classical
  have hY (i : Fin n) := hasInvarianceMoments_gaussianCoordinate (n := n) i
  have hnoise (x : Fin n → ℝ) :
      gaussianNoise ρ (evalMultilinearRV (fourierCoeff f) (fun i z => z i)) x =
        evalMultilinearRV (fourierCoeff (noiseOp ρ f)) (fun i z => z i) x := by
    rw [gaussianNoise_multilinear _ hρ]
    simp only [evalMultilinearRV, noiseOp_fourier, Finset.prod_mul_distrib,
      Finset.prod_const]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  simp_rw [gaussianNoiseStability, hnoise]
  rw [MultilinearMoments.integral_eval_mul (fourierCoeff f)
    (fourierCoeff (noiseOp ρ f)) (fun (i : Fin n) (z : Fin n → ℝ) => z i)
    gaussianCoordinates_independent (fun i => (hY i).reasonable.memLp)
    (fun i => (hY i).mean) (fun i => (hY i).second)]
  exact (plancherel f (noiseOp ρ f)).symm

end BooleanAnalysis.GaussianSpace.MajorityIsStablest
