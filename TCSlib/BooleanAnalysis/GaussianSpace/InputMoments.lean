/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Inputs
import TCSlib.BooleanAnalysis.GaussianSpace.Definitions
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Distributions.Uniform

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian and Boolean input moments

## Main definitions

This module uses the existing standard Gaussian law, Boolean signs, and
fourth-order invariance moment predicate; it introduces no new input laws.

## Main results

* The standard Gaussian has second, third, and fourth moments one, zero, and three.
* Standard Gaussian coordinates satisfy the fourth-order invariance hypotheses.
* Mean-zero signs, including uniform Boolean signs, satisfy the same hypotheses.

These instances supply the input laws for the normalized-bit approximation in
Gaussian Bobkov. Finite fourth moments are established separately from moment
identities, so the totalized integral does not conceal a missing integrability fact.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Fact 11.4, and §11.6, Hypothesis 11.65.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- The fourth moment of a standard Gaussian is three. [OD14, Fact 11.4]

**Proof sketch.** Differentiate the Gaussian moment-generating function
exp(t²/2) four times at zero. Mathlib identifies its derivative with the fourth
moment because the moment-generating function is finite in a neighborhood of zero. -/
lemma integral_fourth_standardGaussian :
    (∫ x : ℝ, x ^ 4 ∂standardGaussianMeasure) = 3 := by
  have h₀ (x : ℝ) :
      HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2))
        (x * Real.exp (x ^ 2 / 2)) x := by
    convert (((hasDerivAt_id x).pow 2).div_const 2).exp using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  have h₁ (x : ℝ) :
      HasDerivAt (fun t : ℝ => t * Real.exp (t ^ 2 / 2))
        ((1 + x ^ 2) * Real.exp (x ^ 2 / 2)) x := by
    convert (hasDerivAt_id x).mul (h₀ x) using 1
    simp only [id_eq]
    ring
  have h₂ (x : ℝ) :
      HasDerivAt (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2))
        ((3 * x + x ^ 3) * Real.exp (x ^ 2 / 2)) x := by
    convert ((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)).mul (h₀ x)
      using 1
    simp only [Pi.pow_apply, Pi.add_apply, id_eq]
    ring
  have hm := ProbabilityTheory.iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := standardGaussianMeasure)
    (by simp [standardGaussianMeasure]) 4
  simp only [Pi.pow_apply] at hm
  rw [← hm, standardGaussianMeasure, ProbabilityTheory.mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul,
    iteratedDeriv_succ, iteratedDeriv_zero]
  rw [funext (fun x => (h₀ x).deriv),
    funext (fun x => (h₁ x).deriv),
    funext (fun x => (h₂ x).deriv)]
  convert ((((hasDerivAt_const (0 : ℝ) (3 : ℝ)).mul (hasDerivAt_id 0)).add
    ((hasDerivAt_id (0 : ℝ)).pow 3)).mul (h₀ 0)).deriv using 1
  norm_num

/-- The third moment of a standard Gaussian vanishes. [OD14, Fact 11.4]

**Proof sketch.** Negation preserves the standard Gaussian law and reverses the
cubic integrand, so its integral equals its own negative. -/
lemma integral_third_standardGaussian :
    (∫ x : ℝ, x ^ 3 ∂standardGaussianMeasure) = 0 := by
  have hmap : standardGaussianMeasure.map (fun x : ℝ => -x) = standardGaussianMeasure := by
    simpa only [standardGaussianMeasure, neg_zero] using
      ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := 1)
  have h := integral_map_of_stronglyMeasurable (μ := standardGaussianMeasure)
    measurable_neg (show StronglyMeasurable (fun x : ℝ => x ^ 3) from by fun_prop)
  rw [hmap] at h
  simp_rw [show ∀ x : ℝ, (-x) ^ 3 = -(x ^ 3) from fun x => by ring] at h
  rw [integral_neg] at h
  linarith

/-- The second moment of a standard Gaussian is one. [OD14, Fact 11.4]

**Proof sketch.** The standard Gaussian has mean zero and variance one; expand
the variance as the integral of the centered square. -/
lemma integral_second_standardGaussian :
    (∫ x : ℝ, x ^ 2 ∂standardGaussianMeasure) = 1 := by
  have h := ProbabilityTheory.variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [ProbabilityTheory.variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable] at h
  simpa [standardGaussianMeasure] using h

/-- A standard Gaussian coordinate satisfies the fourth-order invariance moment
hypotheses. [OD14, Hyp. 11.65]

**Proof sketch.** Combine its moments zero, one, zero, and three with Mathlib's
finite fourth-moment theorem. The reasonability bound is three at most nine. -/
lemma hasInvarianceMoments_standardGaussian :
    HasInvarianceMoments (fun x : ℝ => x) standardGaussianMeasure := by
  refine ⟨⟨?_, by norm_num, ?_, ?_⟩, ?_, integral_second_standardGaussian,
    integral_third_standardGaussian⟩
  · unfold standardGaussianMeasure
    infer_instance
  · simpa only [standardGaussianMeasure] using
      ProbabilityTheory.memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by norm_num)
  · norm_num [ProbabilityTheory.moment, integral_fourth_standardGaussian,
      integral_second_standardGaussian]
  · simp [standardGaussianMeasure]

/-- Any measurable, mean-zero random sign on a probability space satisfies the
fourth-order invariance moment hypotheses. [OD14, Hyp. 11.65]

**Proof sketch.** A function whose square is one is bounded by one in absolute
value, hence has finite fourth moment. Its second and fourth powers are one,
and its third power equals itself. These identities give the required moments. -/
lemma hasInvarianceMoments_of_sq_eq_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) (hmean : (∫ ω, X ω ∂μ) = 0)
    (hsq : ∀ ω, X ω ^ 2 = 1) : HasInvarianceMoments X μ := by
  have hfour (ω) : X ω ^ 4 = 1 := by
    calc
      _ = (X ω ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hsq]; norm_num
  have hnorm (ω) : ‖X ω‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by nlinarith [hsq ω], by nlinarith [hsq ω]⟩
  refine ⟨⟨inferInstance, by norm_num, MemLp.of_bound hX 1 (Eventually.of_forall hnorm), ?_⟩,
    hmean, ?_, ?_⟩
  · norm_num [ProbabilityTheory.moment, Pi.pow_apply, hfour, hsq]
  · simp [hsq]
  · simpa only [pow_succ, hsq, one_mul] using hmean

/-- A uniform Boolean sign satisfies the fourth-order invariance moment
hypotheses. [OD14, Hyp. 11.65]

**Proof sketch.** The two signs have equal probability, so their mean is zero;
each has square one. Apply the general random-sign criterion. -/
lemma hasInvarianceMoments_uniformBool :
    HasInvarianceMoments boolToSign (PMF.uniformOfFintype Bool).toMeasure := by
  apply hasInvarianceMoments_of_sq_eq_one
    (measurable_of_finite boolToSign).aestronglyMeasurable
  · simp [integral_fintype, Measure.real,
      PMF.uniformOfFintype_apply, boolToSign]
  · intro b
    cases b <;> norm_num [boolToSign]

end BooleanAnalysis.GaussianSpace
