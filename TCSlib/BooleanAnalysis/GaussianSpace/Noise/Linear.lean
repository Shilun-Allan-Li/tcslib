/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.Rotation
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Linear symmetries of Gaussian noise

## Main definitions

The existing finite product standard Gaussian laws are reused.

## Main results

* `measurePreserving_gaussianNeg`: simultaneous coordinate sign reversal.
* `measurePreserving_gaussianReflection`: reflection of an independent Gaussian pair.
* `correlatedGaussianMeasure_zero`: independence at correlation zero.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Fact 11.7 and Remark 11.11.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Simultaneous sign reversal preserves the standard Gaussian product law.
[OD14, §11.1, symmetry of the standard Gaussian]

**Proof sketch.** Each centered real Gaussian is invariant under negation.
Take the finite product of these measure-preserving coordinate maps. -/
lemma measurePreserving_gaussianNeg :
    MeasurePreserving (fun x : Fin n → ℝ => -x)
      (Measure.pi fun _ : Fin n => standardGaussianMeasure)
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  apply measurePreserving_pi
  intro i
  refine ⟨measurable_neg, ?_⟩
  simpa only [standardGaussianMeasure, neg_zero] using
    (gaussianReal_map_neg (μ := 0) (v := 1))

/-- Applying the same planar reflection to every coordinate pair preserves the
independent product Gaussian law.
[OD14, Fact 11.7; Remark 11.11]

**Proof sketch.** Rotate the pair by the specified angle, then negate the second
output. Both operations preserve the independent product Gaussian law. -/
lemma measurePreserving_gaussianReflection (θ : ℝ) :
    MeasurePreserving
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i,
         fun i => Real.sin θ * z.1 i - Real.cos θ * z.2 i))
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure))
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure)) := by
  convert ((MeasurePreserving.id
    (Measure.pi fun _ : Fin n => standardGaussianMeasure)).prod
      measurePreserving_gaussianNeg).comp
    (measurePreserving_gaussianRotation θ) using 1
  ext z i <;> simp [ContinuousLinearMap.rotation_apply]
  ring

/-- The characteristic function of a real standard Gaussian at a linear functional
depends only on that functional's value at one. [OD14, §11.1, Gaussian laws] -/
lemma charFunDual_standardGaussian (L : ℝ →L[ℝ] ℝ) :
    charFunDual standardGaussianMeasure L =
      Complex.exp (-((L 1 : ℝ) : ℂ) ^ 2 / 2) := by
  rw [charFunDual_eq_charFun_map_one]
  have hL : (L : ℝ → ℝ) = fun x => L 1 * x := by
    funext x
    simpa only [smul_eq_mul, mul_one, mul_comm] using L.map_smul x (1 : ℝ)
  rw [hL, standardGaussianMeasure, gaussianReal_map_const_mul, charFun_gaussianReal]
  simp [neg_div]

/-- The characteristic function of independent standard Gaussian coordinates is
determined by the sum of the squared coordinate coefficients.
[OD14, §11.1, Gaussian linear combinations]

**Proof sketch.** Independence factors the characteristic function over the
coordinates. Each factor is a scalar Gaussian characteristic function; multiply
the exponentials by adding their quadratic exponents. -/
lemma charFunDual_gaussianPi (L : (Fin n → ℝ) →L[ℝ] ℝ) :
    charFunDual (Measure.pi fun _ : Fin n => standardGaussianMeasure) L =
      Complex.exp (-((∑ i, L (Pi.single i 1) ^ 2 : ℝ) : ℂ) / 2) := by
  rw [charFunDual_pi]
  simp_rw [charFunDual_standardGaussian]
  rw [← Complex.exp_sum]
  congr 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply,
    Complex.ofReal_sum, Complex.ofReal_pow]
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

/-- Expanding the squared coefficients of a pair of projections gives its Gram form. -/
lemma sum_sq_projectionCoefficients (a b : Fin n → ℝ) (u v : ℝ) :
    ∑ i, (u * a i + v * b i) ^ 2 =
      u ^ 2 * ∑ i, a i ^ 2 + 2 * u * v * ∑ i, a i * b i +
        v ^ 2 * ∑ i, b i ^ 2 := by
  calc
    _ = ∑ i, (u ^ 2 * a i ^ 2 + 2 * u * v * (a i * b i) +
        v ^ 2 * b i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- A real linear functional on a pair is given by its two coordinate coefficients. -/
lemma realLinearFunctional_pair (L : (ℝ × ℝ) →L[ℝ] ℝ) (x y : ℝ) :
    L (x, y) = x * L (1, 0) + y * L (0, 1) := by
  have h : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
  rw [h, map_add, map_smul, map_smul]
  rfl

/-- The Euclidean characteristic function of independent standard Gaussian
coordinates is the exponential of minus half the squared norm.
[OD14, §11.1, Gaussian characteristic functions]

**Proof sketch.** Factor the characteristic function over coordinates, use the
scalar Gaussian formula, and identify the sum of squares with the Euclidean norm. -/
lemma charFun_gaussianEuclidean (t : EuclideanSpace ℝ (Fin n)) :
    charFun ((Measure.pi fun _ : Fin n => standardGaussianMeasure).map
      (WithLp.toLp 2)) t = Complex.exp (-((‖t‖ ^ 2 : ℝ) : ℂ) / 2) := by
  rw [charFun_pi]
  simp_rw [standardGaussianMeasure, charFun_gaussianReal]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one,
    one_mul, zero_sub, neg_div]
  rw [← Complex.exp_sum]
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, Complex.ofReal_sum, Complex.ofReal_pow]
  rw [Finset.sum_neg_distrib, ← Finset.sum_div]

/-- An orthogonal transformation preserves the Euclidean standard Gaussian law.
[OD14, §11.1, orthogonal invariance]

**Proof sketch.** Precomposing a characteristic function with the orthogonal
map evaluates the original function at the inverse transform. The Gaussian
characteristic function depends only on the norm, which the inverse preserves. -/
lemma measurePreserving_gaussianEuclideanIsometry
    (Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving Q
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).map (WithLp.toLp 2))
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).map (WithLp.toLp 2)) := by
  refine ⟨Q.continuous.measurable, ?_⟩
  apply Measure.ext_of_charFun
  ext t
  calc
    _ = charFun
        ((Measure.pi fun _ : Fin n => standardGaussianMeasure).map (WithLp.toLp 2))
        (Q.symm t) := by
      rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_apply]
      congr 1
      funext x
      rw [Q.inner_map_eq_flip]
    _ = _ := by
      rw [charFun_gaussianEuclidean, charFun_gaussianEuclidean, Q.symm.norm_map]

/-- Expressing an orthogonal transformation in ordinary coordinates preserves
the finite product standard Gaussian law. [OD14, §11.1, orthogonal invariance] -/
lemma measurePreserving_gaussianIsometry
    (Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (fun x => WithLp.ofLp (Q (WithLp.toLp 2 x)))
      (Measure.pi fun _ : Fin n => standardGaussianMeasure)
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  let e := MeasurableEquiv.toLp 2 (Fin n → ℝ)
  have he := e.measurable.measurePreserving
    (Measure.pi fun _ : Fin n => standardGaussianMeasure)
  exact (MeasurePreserving.symm e he).comp
    ((measurePreserving_gaussianEuclideanIsometry Q).comp he)

/-- A correlated linear combination of two independent standard Gaussian vectors
is standard Gaussian. [OD14, Fact 11.7]

**Proof sketch.** This is the first coordinate of a Gaussian rotation by the
arccosine of the correlation. -/
lemma measurePreserving_gaussianEndpoint {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    MeasurePreserving
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i)
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure))
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  simpa only [Function.comp_def, ContinuousLinearMap.rotation_apply,
    Real.cos_arccos hρ.1 hρ.2, Real.sin_arccos, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] using
    (measurePreserving_fst.comp
      (measurePreserving_gaussianRotation (n := n) (Real.arccos ρ)))

/-- A unit linear combination with nonnegative second coefficient preserves the
standard Gaussian law. [OD14, Fact 11.7] -/
lemma measurePreserving_gaussianCombination (b c : ℝ) (hc : 0 ≤ c)
    (hbc : b ^ 2 + c ^ 2 = 1) :
    MeasurePreserving
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => fun i => b * z.1 i + c * z.2 i)
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure))
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  have hb : b ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg c]
  have hs : Real.sqrt (1 - b ^ 2) = c :=
    (Real.sqrt_eq_iff_eq_sq (by nlinarith [sq_nonneg c]) hc).2 (by linarith)
  simpa only [hs] using (measurePreserving_gaussianEndpoint (n := n) hb)

/-- The product of two valid Gaussian correlations is a valid correlation. -/
lemma correlation_mul_mem {ρ σ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hσ : σ ∈ Set.Icc (-1 : ℝ) 1) :
    ρ * σ ∈ Set.Icc (-1 : ℝ) 1 := by
  apply abs_le.mp
  rw [abs_mul]
  exact (mul_le_mul (abs_le.mpr hρ) (abs_le.mpr hσ) (abs_nonneg σ) zero_le_one).trans
    (by norm_num)

/-- The variances of the two increments in a composed Gaussian kernel add to
the variance at the product correlation. [OD14, §11.1, Mehler semigroup] -/
lemma gaussianNoise_increment_variance {ρ σ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hσ : σ ∈ Set.Icc (-1 : ℝ) 1) :
    (σ * Real.sqrt (1 - ρ ^ 2)) ^ 2 + Real.sqrt (1 - σ ^ 2) ^ 2 =
      Real.sqrt (1 - (ρ * σ) ^ 2) ^ 2 := by
  have hnonneg {r : ℝ} (hr : r ∈ Set.Icc (-1 : ℝ) 1) : 0 ≤ 1 - r ^ 2 :=
    sub_nonneg.mpr ((sq_le_one_iff_abs_le_one r).2 (abs_le.mpr hr))
  rw [mul_pow, Real.sq_sqrt (hnonneg hρ), Real.sq_sqrt (hnonneg hσ),
    Real.sq_sqrt (hnonneg (correlation_mul_mem hρ hσ))]
  ring

/-- At correlation zero the two endpoints are independent standard Gaussian
vectors. [OD14, Def. 11.10] -/
lemma correlatedGaussianMeasure_zero {n : ℕ} :
    correlatedGaussianMeasure (n := n) 0 =
      (Measure.pi (fun _ : Fin n => standardGaussianMeasure)).prod
        (Measure.pi (fun _ : Fin n => standardGaussianMeasure)) := by
  simp [correlatedGaussianMeasure]

end BooleanAnalysis.GaussianSpace
