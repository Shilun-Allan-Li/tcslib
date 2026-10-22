/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise.BooleanCharacteristic
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Torus
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.MetricSpace.Equicontinuity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform extension of Gaussian Fourier transfer

## Main definitions

Bounded linear expectation functionals express the Boolean block coupling and
the correlated Gaussian coupling on the compact torus.

* `gaussianPairTorusMap`: the compact image of a pair of real vectors.
* `booleanBlockExpectation`: normalized Boolean block expectation as a linear functional.
* `compactIntegralCLM`: integration of continuous functions against a finite compact measure.

## Main results

* `tendsto_clm_of_dense_span`: a common norm bound extends convergence from
  a dense linear span to the entire space.
* `tendsto_booleanBlockExpectation`: every continuous joint torus observable
  converges to its correlated Gaussian expectation.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, BitsToGaussians and Gaussian Hypercontractivity.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open Hypercontractivity ThresholdFunctions

variable {n : ℕ}

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))

local instance (ρ : ℝ) : IsFiniteMeasure (correlatedGaussianMeasure (n := n) ρ) := by
  unfold correlatedGaussianMeasure
  infer_instance

/-- Record both real endpoints in the disjoint coordinate halves of one compact
torus, using the two-frequency map for each endpoint. -/
noncomputable def gaussianPairTorusMap (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)) :=
  Sum.elim (gaussianTorusMap z.1) (gaussianTorusMap z.2)

/-- The joint torus map is continuous. -/
@[fun_prop]
lemma continuous_gaussianPairTorusMap : Continuous (gaussianPairTorusMap (n := n)) := by
  apply continuous_pi
  rintro (i | i)
  · change Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => gaussianTorusMap z.1 i)
    fun_prop
  · change Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => gaussianTorusMap z.2 i)
    fun_prop

/-- A joint torus character is a linear phase of the two real endpoints.

**Proof sketch.** Split the character product over the two coordinate halves,
apply the one-endpoint phase identity, and combine the two exponentials. -/
lemma mFourier_gaussianPairTorusMap
    (m : ((Fin n × Bool) ⊕ (Fin n × Bool)) → ℤ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    UnitAddTorus.mFourier m (gaussianPairTorusMap z) =
      Complex.exp (((∑ i,
        (gaussianTorusFrequency (fun j => m (.inl j)) i * z.1 i +
          gaussianTorusFrequency (fun j => m (.inr j)) i * z.2 i) : ℝ) : ℂ) * Complex.I) := by
  change (∏ j, fourier (m j) (gaussianPairTorusMap z j)) = _
  rw [Fintype.prod_sum_type]
  change UnitAddTorus.mFourier (fun j => m (.inl j)) (gaussianTorusMap z.1) *
    UnitAddTorus.mFourier (fun j => m (.inr j)) (gaussianTorusMap z.2) = _
  rw [mFourier_gaussianTorusMap, mFourier_gaussianTorusMap, ← Complex.exp_add]
  congr 1
  simp only [gaussianTorusFrequency, Finset.sum_add_distrib, Complex.ofReal_add, add_mul]

/-- A Boolean noise expectation is bounded by a uniform bound for its integrand.

**Proof sketch.** All kernel weights are nonnegative. The triangle inequality
reduces the estimate to their total mass, which is one. -/
lemma norm_booleanNoiseExpectation_le {N : ℕ} {ρ C : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (F : BoolCube N → BoolCube N → ℂ) (hF : ∀ x y, ‖F x y‖ ≤ C) :
    ‖(uniformWeight N : ℂ) * (∑ x, ∑ y, (noiseKernel ρ x y : ℂ) * F x y)‖ ≤ C := by
  have hw : 0 ≤ uniformWeight N := by unfold uniformWeight; positivity
  calc
    _ = uniformWeight N * ‖∑ x, ∑ y, (noiseKernel ρ x y : ℂ) * F x y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    _ ≤ uniformWeight N * (∑ x : BoolCube N, ∑ y : BoolCube N, noiseKernel ρ x y * C) := by
      apply mul_le_mul_of_nonneg_left _ hw
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (noiseKernel_nonneg hρ0 hρ1 x y)]
      exact mul_le_mul_of_nonneg_left (hF x y) (noiseKernel_nonneg hρ0 hρ1 x y)
    _ = C := by
      simp only [← Finset.sum_mul, noiseKernel_sum_right hρ0 hρ1]
      rw [← mul_assoc]
      have hmass : uniformWeight N * (∑ _x : BoolCube N, (1 : ℝ)) = 1 :=
        by simp [uniformWeight, inv_pow]
      rw [hmass, one_mul]

/-- The Boolean block expectation, as a bounded linear functional on the
continuous functions of the joint torus. -/
noncomputable def booleanBlockExpectation (n m : ℕ) (ρ : ℝ) :
    C(UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)), ℂ) →L[ℂ] ℂ :=
  (uniformWeight (n * m) : ℂ) •
    ∑ x : BoolCube (n * m), ∑ y : BoolCube (n * m),
      (noiseKernel ρ x y : ℂ) • ContinuousMap.evalCLM (R := ℂ)
        (gaussianPairTorusMap (normalizedCubeBlocks n m x, normalizedCubeBlocks n m y))

/-- Evaluation of the block expectation is the explicit positive-kernel sum. -/
lemma booleanBlockExpectation_apply (n m : ℕ) (ρ : ℝ)
    (F : C(UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)), ℂ)) :
    booleanBlockExpectation n m ρ F = (uniformWeight (n * m) : ℂ) *
      (∑ x : BoolCube (n * m), ∑ y : BoolCube (n * m), (noiseKernel ρ x y : ℂ) *
        F (gaussianPairTorusMap (normalizedCubeBlocks n m x, normalizedCubeBlocks n m y))) := by
  simp [booleanBlockExpectation, smul_eq_mul]

/-- Each block expectation has operator norm at most one. -/
lemma norm_booleanBlockExpectation_le (n m : ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (F : C(UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)), ℂ)) :
    ‖booleanBlockExpectation n m ρ F‖ ≤ ‖F‖ := by
  rw [booleanBlockExpectation_apply]
  exact norm_booleanNoiseExpectation_le hρ0 hρ1 _
    (fun x y => F.norm_coe_le_norm _)

/-- Integration against a finite measure on a compact space, as a bounded
complex linear functional. -/
noncomputable def compactIntegralCLM {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] : C(X, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫ x, F x ∂μ
      map_add' := fun F G => integral_add ((BoundedContinuousFunction.mkOfCompact F).integrable μ)
        ((BoundedContinuousFunction.mkOfCompact G).integrable μ)
      map_smul' := fun c F => integral_smul c F }
    (μ Set.univ).toReal (fun F => by
      simpa only [mul_comm] using norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun x => F.norm_coe_le_norm x))

/-- The compact integration functional agrees with the ordinary Bochner integral. -/
lemma compactIntegralCLM_apply {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (F : C(X, ℂ)) :
    compactIntegralCLM μ F = ∫ x, F x ∂μ := rfl

/-- Convergence of uniformly bounded complex linear functionals on a dense
generating family extends to every vector.

**Proof sketch.** Linearity extends convergence to the span. The common norm
bound gives equicontinuity, so the set where convergence holds is closed. -/
lemma tendsto_clm_of_dense_span {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : ℕ → E →L[ℂ] ℂ) (M : E →L[ℂ] ℂ) (C : ℝ)
    (hbound : ∀ m x, ‖L m x‖ ≤ C * ‖x‖) {s : Set E}
    (hdense : Dense (Submodule.span ℂ s : Set E))
    (hgen : ∀ x ∈ s, Tendsto (fun m => L m x) atTop (𝓝 (M x))) (x : E) :
    Tendsto (fun m => L m x) atTop (𝓝 (M x)) := by
  have hequi : Equicontinuous (fun m x => L m x) :=
    Metric.equicontinuous_of_continuity_modulus (fun t => C * t)
      (by simpa only [mul_zero] using
        ((by fun_prop : Continuous (fun t : ℝ => C * t)).tendsto 0)) _
      (fun x y m => by simpa only [dist_eq_norm, ← map_sub] using hbound m (x - y))
  have hspan : ∀ x ∈ Submodule.span ℂ s,
      Tendsto (fun m => L m x) atTop (𝓝 (M x)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => simpa only [map_zero] using (tendsto_const_nhds (x := (0 : ℂ)))
    | add x y _ _ hx hy => simpa only [map_add] using hx.add hy
    | smul c x _ hx => simpa only [map_smul] using hx.const_smul c
  exact closure_minimal hspan (hequi.isClosed_setOf_tendsto M.continuous) (hdense x)

/-- Every continuous joint torus observable has the Gaussian limit under
normalized correlated Boolean blocks.
[OD14, §11.1, BitsToGaussians]

**Proof sketch.** Character expectations converge by the explicit covariance
calculation. Characters have dense span in the uniform norm, and both expectation
functionals are continuous with a common norm bound. -/
lemma tendsto_booleanBlockExpectation {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (F : C(UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)), ℂ)) :
    Tendsto (fun m : ℕ => booleanBlockExpectation n m ρ F) atTop
      (𝓝 (∫ z : (Fin n → ℝ) × (Fin n → ℝ),
        F (gaussianPairTorusMap z) ∂correlatedGaussianMeasure ρ)) := by
  let μ := (correlatedGaussianMeasure (n := n) ρ).map gaussianPairTorusMap
  have hM (G : C(UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)), ℂ)) :
      compactIntegralCLM μ G = ∫ z, G (gaussianPairTorusMap z) ∂correlatedGaussianMeasure ρ := by
    rw [compactIntegralCLM_apply]
    exact integral_map continuous_gaussianPairTorusMap.aemeasurable
      G.continuous.aestronglyMeasurable
  rw [← hM]
  apply tendsto_clm_of_dense_span (fun m => booleanBlockExpectation n m ρ)
    (compactIntegralCLM μ) 1
    (fun m G => by simpa only [one_mul] using norm_booleanBlockExpectation_le n m hρ0 hρ1 G)
    (s := Set.range UnitAddTorus.mFourier)
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
      UnitAddTorus.span_mFourier_closure_eq_top
  · rintro _ ⟨m, rfl⟩
    simp only [hM, booleanBlockExpectation_apply, mFourier_gaussianPairTorusMap]
    exact tendsto_sum_noiseKernel_normalizedCubeBlocks_phase ⟨by linarith, hρ1⟩ _ _

/-- The joint compact transfer statement for real observables. -/
lemma tendsto_booleanBlockExpectation_real {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (F : C(UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)), ℝ)) :
    Tendsto (fun m : ℕ => uniformWeight (n * m) *
      (∑ x : BoolCube (n * m), ∑ y : BoolCube (n * m), noiseKernel ρ x y *
        F (gaussianPairTorusMap (normalizedCubeBlocks n m x, normalizedCubeBlocks n m y))))
      atTop (𝓝 (∫ z : (Fin n → ℝ) × (Fin n → ℝ),
        F (gaussianPairTorusMap z) ∂correlatedGaussianMeasure ρ)) := by
  let G : C(UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)), ℂ) :=
    ⟨fun z => (F z : ℂ), Complex.continuous_ofReal.comp F.continuous⟩
  have ht := tendsto_booleanBlockExpectation hρ0 hρ1 G
  simp only [booleanBlockExpectation_apply, G, ContinuousMap.coe_mk,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum] at ht
  rw [integral_complex_ofReal] at ht
  simpa only [Function.comp_def, Complex.ofReal_re] using
    Complex.continuous_re.tendsto _ |>.comp ht

end BooleanAnalysis.GaussianSpace
