/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Basis

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian noise and the Hermite spectrum

## Main definitions

The normalized Hermite functions, Gaussian noise operator, and correlated
Gaussian measure are reused from the preceding modules.

## Main results

Gaussian affine averaging of scalar Hermite polynomials yields the multivariate
noise eigenfunction identity and the degree multipliers of Hermite coefficients.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Propositions 11.31 and 11.37.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))

/-- Gaussian affine Hermite averages satisfy the retained-correlation recurrence.
[OD14, Prop. 11.37, scalar polynomial identity]

**Proof sketch.** Expand the Hermite recurrence under the integral. Transfer the
noise-coordinate factor to a derivative by Gaussian integration by parts, use
the Hermite lowering formula, and simplify with the variance identity. -/
private lemma integral_hermite_affine_recurrence
    (k : ℕ) (ρ s x : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) :
    (∫ y : ℝ, Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite (k + 2))
      ∂standardGaussianMeasure) =
      ρ * x * (∫ y : ℝ,
        Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite (k + 1))
        ∂standardGaussianMeasure) -
      ((k + 1 : ℕ) : ℝ) * ρ ^ 2 * (∫ y : ℝ,
        Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite k)
        ∂standardGaussianMeasure) := by
  have hint (j : ℕ) :
      Integrable (fun y : ℝ =>
        Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite j))
        standardGaussianMeasure ∧
      Integrable (fun y : ℝ =>
        y * Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite j))
        standardGaussianMeasure := by
    constructor
    · simpa only [Polynomial.eval_one, one_mul, Polynomial.eval_map,
        Polynomial.aeval_def] using
        integrable_polynomial_mul_affine_standardGaussian
          ((Polynomial.hermite j).map (Int.castRingHom ℝ)) 1 (ρ * x) s
    · simpa only [Polynomial.eval_X, Polynomial.eval_map, Polynomial.aeval_def] using
        integrable_polynomial_mul_affine_standardGaussian
          ((Polynomial.hermite j).map (Int.castRingHom ℝ)) Polynomial.X (ρ * x) s
  have hstein :
      (∫ y : ℝ, y * Polynomial.aeval (ρ * x + s * y)
        (Polynomial.hermite (k + 1)) ∂standardGaussianMeasure) =
      s * ((k + 1 : ℕ) : ℝ) *
        ∫ y : ℝ, Polynomial.aeval (ρ * x + s * y)
          (Polynomial.hermite k) ∂standardGaussianMeasure := by
    have h := integral_id_mul_polynomial_affine_standardGaussian
      ((Polynomial.hermite (k + 1)).map (Int.castRingHom ℝ)) (ρ * x) s
    simp_rw [Polynomial.derivative_map, derivative_hermite_succ,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C,
      map_natCast, Polynomial.eval_map] at h
    simpa only [Polynomial.aeval_def, algebraMap_int_eq, integral_const_mul,
      mul_assoc] using h
  have hpoint (y : ℝ) :
      Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite (k + 2)) =
        (ρ * x) * Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite (k + 1)) +
        s * (y * Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite (k + 1))) -
        ((k + 1 : ℕ) : ℝ) *
          Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite k) := by
    rw [Polynomial.hermite_succ, derivative_hermite_succ]
    simp only [map_sub, map_mul, Polynomial.aeval_X, map_natCast]
    ring
  simp_rw [hpoint]
  rw [integral_sub
    (f := fun y : ℝ =>
      (ρ * x) * Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite (k + 1)) +
      s * (y * Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite (k + 1))))
    (g := fun y : ℝ => ((k + 1 : ℕ) : ℝ) *
      Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite k))
    (by simpa only [Pi.add_apply] using
      (((hint (k + 1)).1.const_mul (ρ * x)).add ((hint (k + 1)).2.const_mul s)))
    ((hint k).1.const_mul ((k + 1 : ℕ) : ℝ)),
    integral_add
      (f := fun y : ℝ =>
        (ρ * x) * Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite (k + 1)))
      (g := fun y : ℝ =>
        s * (y * Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite (k + 1))))
      ((hint (k + 1)).1.const_mul (ρ * x))
      ((hint (k + 1)).2.const_mul s)]
  simp only [integral_const_mul]
  rw [hstein]
  nlinarith [congrArg (fun t : ℝ => ((k + 1 : ℕ) : ℝ) *
    (∫ y : ℝ, Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite k)
      ∂standardGaussianMeasure) * t) hρs]

/-- Averaging a probabilists' Hermite polynomial along a Gaussian affine map
scales it by the corresponding power of the retained correlation.
[OD14, Prop. 11.37, scalar polynomial identity]

**Proof sketch.** Gaussian integration by parts and the Hermite lowering identity
give the same two-step recurrence for the Gaussian averages and the claimed
values. Their constant and linear initial values agree. -/
lemma integral_hermite_affine_standardGaussian
    (k : ℕ) (ρ s x : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) :
    (∫ y : ℝ, Polynomial.aeval (ρ * x + s * y) (Polynomial.hermite k)
      ∂standardGaussianMeasure) =
      ρ ^ k * Polynomial.aeval x (Polynomial.hermite k) := by
  induction k using Nat.twoStepInduction with
  | zero =>
      simp [Polynomial.hermite_zero]
  | one =>
      have hid : Integrable (fun y : ℝ => y) standardGaussianMeasure :=
        memLp_one_iff_integrable.mp
          (ProbabilityTheory.memLp_id_gaussianReal' 1 (by norm_num))
      simp only [Polynomial.hermite_one, Polynomial.aeval_X, pow_one]
      rw [integral_add (integrable_const (ρ * x)) (hid.const_mul s),
        integral_const_mul s (fun y : ℝ => y)]
      simp [standardGaussianMeasure]
  | more k ihk ihk1 =>
      rw [integral_hermite_affine_recurrence k ρ s x hρs, ihk1, ihk,
        Polynomial.hermite_succ (k + 1), derivative_hermite_succ]
      simp only [map_sub, map_mul, Polynomial.aeval_X, map_natCast, pow_succ]
      ring

/-- Gaussian affine averaging multiplies the normalized scalar Hermite polynomial
by correlation to its degree. [OD14, Prop. 11.37]

**Proof sketch.** Pull the constant factorial normalization through the
unnormalized Hermite averaging identity. -/
lemma integral_normalizedHermite_affine_standardGaussian
    (k : ℕ) (ρ s x : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) :
    (∫ y : ℝ, (normalizedHermitePolynomial k).eval (ρ * x + s * y)
      ∂standardGaussianMeasure) =
      ρ ^ k * (normalizedHermitePolynomial k).eval x := by
  have h := integral_hermite_affine_standardGaussian k ρ s x hρs
  simp only [Polynomial.aeval_def, algebraMap_int_eq] at h
  simp only [normalizedHermitePolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_map]
  rw [integral_const_mul, h]
  ring

/-- Hermite functions are Gaussian noise eigenfunctions of their total degree.
[OD14, Prop. 11.37] **Proof sketch.** Apply the scalar conditional Hermite
identity coordinatewise and integrate the independent noise coordinates. -/
theorem gaussianNoise_hermiteFunction (α : Fin n → ℕ) (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    gaussianNoise ρ (hermiteFunction α) =
      fun x => ρ ^ (∑ i, α i) * hermiteFunction α x := by
  have hρs : ρ ^ 2 + (Real.sqrt (1 - ρ ^ 2)) ^ 2 = 1 := by
    rw [Real.sq_sqrt (show 0 ≤ 1 - ρ ^ 2 by nlinarith [hρ.1, hρ.2])]
    ring
  funext x
  simp only [gaussianNoise, hermiteFunction_eq_prod]
  rw [integral_fintype_prod_eq_prod (fun (i : Fin n) (y : ℝ) =>
    (normalizedHermitePolynomial (α i)).eval
      (ρ * x i + Real.sqrt (1 - ρ ^ 2) * y))]
  simp_rw [integral_normalizedHermite_affine_standardGaussian
    _ ρ (Real.sqrt (1 - ρ ^ 2)) _ hρs]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- The correlated moment of two Hermite functions vanishes off the diagonal;
on the diagonal it is correlation raised to total degree.
[OD14, Prop. 11.31 and its coordinate-product consequence]

**Proof sketch.** Write the correlated integral as a Gaussian noise inner
product. Apply the Hermite eigenfunction identity and then orthogonality. -/
theorem hermite_correlated_moment (α β : Fin n → ℕ) (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (∫ z, hermiteFunction α z.1 * hermiteFunction β z.2
      ∂correlatedGaussianMeasure ρ) = if α = β then ρ ^ (∑ i, α i) else 0 := by
  classical
  rw [integral_correlatedGaussianMeasure hρ (hermiteFunction_memLp_two α)
    (hermiteFunction_memLp_two β), gaussianNoise_hermiteFunction β ρ hρ]
  simp_rw [mul_comm (ρ ^ (∑ i, β i)), ← mul_assoc]
  rw [integral_mul_const, integral_hermiteFunction_mul]
  by_cases h : α = β
  · subst β
    simp
  · simp [h]

/-- Gaussian noise multiplies each Hermite coefficient by correlation to degree.
[OD14, Prop. 11.37] **Proof sketch.** Move noise across the coefficient inner
product using self-adjointness, then use the Hermite eigenfunction identity. -/
theorem hermiteCoeff_gaussianNoise (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (α : Fin n → ℕ) :
    hermiteCoeff (gaussianNoise ρ f) α =
      ρ ^ (∑ i, α i) * hermiteCoeff f α := by
  have h := gaussianNoise_selfAdjoint hρ (hermiteFunction_memLp_two α) hf
  rw [gaussianNoise_hermiteFunction α ρ hρ] at h
  simp_rw [mul_assoc] at h
  rw [integral_const_mul] at h
  simpa only [hermiteCoeff, mul_comm] using h

/-- Gaussian stability equals the degree-weighted squared Hermite spectrum.
[OD14, Prop. 11.37] **Proof sketch.** Apply Plancherel to a function and its
noisy version, then insert the coefficient multiplier identity. -/
theorem gaussianNoiseStability_hermite (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    gaussianNoiseStability ρ f =
      ∑' α : Fin n → ℕ, ρ ^ (∑ i, α i) * (hermiteCoeff f α) ^ 2 := by
  rw [gaussianNoiseStability,
    hermite_plancherel f (gaussianNoise ρ f) hf
      (gaussianNoise_memLp hρ 2 (by norm_num) hf)]
  simp_rw [hermiteCoeff_gaussianNoise f hf ρ hρ]
  congr 1
  funext α
  ring

end BooleanAnalysis.GaussianSpace
