/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.NormalizedSums
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian approximation by independent Boolean blocks

## Main definitions

* `normalizedBoolSumLaw`: the probability law of one normalized Boolean block.

## Main results

* Scalar Lipschitz expectation convergence passes to bounded continuous tests
  of every fixed finite product of the input law.
* Independent normalized Boolean blocks approximate the product standard
  Gaussian law for every bounded continuous vector test.

This is the finite-dimensional BitsToGaussians bridge used to transfer Boolean
Bobkov. It reuses Mathlib's characterization of weak convergence by bounded
Lipschitz tests and continuity of finite products of probability measures.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, BitsToGaussians, and §11.4,
  Gaussian Bobkov's inequality.
-/

open MeasureTheory Filter
open scoped BigOperators NNReal ENNReal Topology BoundedContinuousFunction

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- Scalar Lipschitz expectation convergence of probability laws implies
convergence of bounded continuous tests of every fixed finite product.

**Proof sketch.** Bounded Lipschitz tests characterize weak convergence. Apply
continuity of finite products of probability laws, then the characterization
of weak convergence by bounded continuous tests. All latter integrals are finite. -/
lemma tendsto_integral_pi_of_scalar_lipschitz
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hμ : ∀ (c : ℝ≥0) (ψ : ℝ → ℝ), LipschitzWith c ψ →
      Tendsto (fun m => ∫ x : ℝ, ψ x ∂(μ m : Measure ℝ)) atTop
        (𝓝 (∫ x : ℝ, ψ x ∂(ν : Measure ℝ))))
    (n : ℕ) (F : (Fin n → ℝ) →ᵇ ℝ) :
    Tendsto (fun m => ∫ x : Fin n → ℝ, F x
      ∂(Measure.pi fun _ : Fin n => (μ m : Measure ℝ))) atTop
      (𝓝 (∫ x : Fin n → ℝ, F x
        ∂(Measure.pi fun _ : Fin n => (ν : Measure ℝ)))) := by
  have hweak : Tendsto μ atTop (𝓝 ν) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    intro ψ _ hψ
    obtain ⟨c, hc⟩ := hψ
    exact hμ c ψ hc
  have hprod : Tendsto (fun m => ProbabilityMeasure.pi (fun _ : Fin n => μ m)) atTop
      (𝓝 (ProbabilityMeasure.pi fun _ : Fin n => ν)) :=
    (ProbabilityMeasure.continuous_pi.tendsto (fun _ : Fin n => ν)).comp
      (tendsto_pi_nhds.mpr fun _ => hweak)
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hprod F

/-- The law of a normalized sum of m+1 independent uniform Boolean signs,
bundled as a probability measure on the real line.
[OD14, §11.1, BitsToGaussians] -/
noncomputable def normalizedBoolSumLaw (m : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(Measure.pi fun _ : Fin (m + 1) => (PMF.uniformOfFintype Bool).toMeasure).map
      (fun x : Fin (m + 1) → Bool =>
        (∑ i, boolToSign (x i)) / Real.sqrt (m + 1)),
    Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable⟩

/-- Every bounded continuous test of finitely many independent normalized
Boolean sums converges to its expectation under the product standard Gaussian
law. [OD14, §11.1, BitsToGaussians]

**Proof sketch.** Identify scalar integration under the normalized-sum law with
expectation of the normalized Boolean block. The scalar Lipschitz limit and
continuity of finite products give the asserted vector-test limit. -/
lemma tendsto_integral_normalizedBoolSum_pi (n : ℕ) (F : (Fin n → ℝ) →ᵇ ℝ) :
    Tendsto (fun m => ∫ z : Fin n → ℝ, F z
      ∂(Measure.pi fun _ : Fin n => (normalizedBoolSumLaw m : Measure ℝ))) atTop
      (𝓝 (∫ z : Fin n → ℝ, F z
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure))) := by
  let ν : ProbabilityMeasure ℝ := ⟨standardGaussianMeasure, by
    unfold standardGaussianMeasure
    infer_instance⟩
  refine tendsto_integral_pi_of_scalar_lipschitz normalizedBoolSumLaw ν ?_ n F
  intro c ψ hψ
  have he (m : ℕ) : (∫ y : ℝ, ψ y ∂(normalizedBoolSumLaw m : Measure ℝ)) =
      ∫ x : Fin (m + 1) → Bool,
        ψ ((∑ i, boolToSign (x i)) / Real.sqrt (m + 1))
        ∂(Measure.pi fun _ : Fin (m + 1) => (PMF.uniformOfFintype Bool).toMeasure) := by
    exact integral_map_of_stronglyMeasurable (measurable_of_finite _)
      hψ.continuous.stronglyMeasurable
  change Tendsto (fun m => ∫ y : ℝ, ψ y ∂(normalizedBoolSumLaw m : Measure ℝ)) atTop
    (𝓝 (∫ y : ℝ, ψ y ∂standardGaussianMeasure))
  simp_rw [he]
  exact tendsto_integral_normalizedBoolSum c ψ hψ

/-- Bounded continuous tests of independent normalized Boolean blocks converge
to their expectation under the product standard Gaussian law.
[OD14, §11.1, BitsToGaussians]
The integral on the left uses an array of independent Boolean blocks directly.

**Proof sketch.** The product map taking each Boolean block to its normalized
sum pushes the array law to the product of normalized-sum laws. Transfer the
integral through that map and apply the finite-dimensional convergence result. -/
lemma tendsto_integral_normalizedBoolBlocks (n : ℕ) (F : (Fin n → ℝ) →ᵇ ℝ) :
    Tendsto (fun m =>
      ∫ x : Fin n → (Fin (m + 1) → Bool),
        F (fun i => (∑ j, boolToSign (x i j)) / Real.sqrt (m + 1))
        ∂(Measure.pi fun _ : Fin n =>
          Measure.pi fun _ : Fin (m + 1) => (PMF.uniformOfFintype Bool).toMeasure)) atTop
      (𝓝 (∫ z : Fin n → ℝ, F z
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure))) := by
  have he (m : ℕ) : (∫ z : Fin n → ℝ, F z
      ∂(Measure.pi fun _ : Fin n => (normalizedBoolSumLaw m : Measure ℝ))) =
      ∫ x : Fin n → (Fin (m + 1) → Bool),
        F (fun i => (∑ j, boolToSign (x i j)) / Real.sqrt (m + 1))
        ∂(Measure.pi fun _ : Fin n =>
          Measure.pi fun _ : Fin (m + 1) => (PMF.uniformOfFintype Bool).toMeasure) := by
    let ρ : Measure (Fin (m + 1) → Bool) :=
      Measure.pi fun _ : Fin (m + 1) => (PMF.uniformOfFintype Bool).toMeasure
    let f (x : Fin (m + 1) → Bool) := (∑ j, boolToSign (x j)) / Real.sqrt (m + 1)
    haveI : IsProbabilityMeasure (ρ.map f) :=
      Measure.isProbabilityMeasure_map (measurable_of_finite f).aemeasurable
    have hmap := Measure.pi_map_pi (μ := fun _ : Fin n => ρ) (f := fun _ : Fin n => f)
      (fun _ => (measurable_of_finite f).aemeasurable)
    change (∫ z : Fin n → ℝ, F z ∂(Measure.pi fun _ : Fin n => ρ.map f)) =
      ∫ x : Fin n → (Fin (m + 1) → Bool), F (fun i => f (x i))
        ∂(Measure.pi fun _ : Fin n => ρ)
    rw [← hmap]
    exact integral_map_of_stronglyMeasurable (measurable_of_finite _)
      F.continuous.stronglyMeasurable
  simpa only [he] using tendsto_integral_normalizedBoolSum_pi n F

end BooleanAnalysis.GaussianSpace
