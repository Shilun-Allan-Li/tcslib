/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Taylor
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Moments
import Mathlib.Probability.Independence.Integration

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Independent affine replacements

## Main definitions

The existing polynomial evaluation and moment hypotheses are reused.

## Main results

* `independent_affine_integral`: integrate a scalar input separately from its background.
* `independent_affine_comparison_bound`: integrate a pointwise affine comparison.
* `independent_affine_replacement_bound`: integrate the fourth-order replacement error.
* `independent_affine_replacement_bound_c3`: integrate the third-order replacement error.
* `single_coordinate_replacement_bound`: the polynomial replacement estimate in terms of influence.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, proof of the Basic Invariance Principle (11.29).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions Hypercontractivity

/-- For a scalar input independent of an affine background, the test expectation
can be computed by integrating the scalar first and then the background.
The resulting inner-integral function is integrable under the background law.
This is the Fubini step in [OD14, §11.6, proof of (11.29)].

**Proof sketch.** Independence factors the joint law into the two marginal laws.
Transfer test integrability to this product law and apply Fubini. Integration
against the scalar marginal is the same as integration of the original input. -/
theorem independent_affine_integral
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A D W : Ω → ℝ)
    (hAD : AEMeasurable (fun ω => (A ω, D ω)) μ)
    (hW : AEMeasurable W μ)
    (hind : IndepFun W (fun ω => (A ω, D ω)) μ)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (hint : Integrable (fun ω => ψ (A ω + D ω * W ω)) μ) :
    Integrable (fun z : ℝ × ℝ => ∫ ω, ψ (z.1 + z.2 * W ω) ∂μ)
        (μ.map (fun ω => (A ω, D ω))) ∧
      (∫ ω, ψ (A ω + D ω * W ω) ∂μ) =
        ∫ z : ℝ × ℝ, (∫ ω, ψ (z.1 + z.2 * W ω) ∂μ)
          ∂(μ.map (fun ω => (A ω, D ω))) := by
  let f : (ℝ × ℝ) × ℝ → ℝ := fun p => ψ (p.1.1 + p.1.2 * p.2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hpair := hAD.prodMk hW
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hAD hW).mp hind.symm
  haveI := Measure.isProbabilityMeasure_map hAD
  haveI := Measure.isProbabilityMeasure_map hW
  have hfint : Integrable f
      ((μ.map (fun ω => (A ω, D ω))).prod (μ.map W)) := by
    rw [← hlaw]
    exact (integrable_map_measure hf.stronglyMeasurable.aestronglyMeasurable hpair).mpr hint
  have hi (z : ℝ × ℝ) :
      (∫ w, f (z, w) ∂μ.map W) = ∫ ω, ψ (z.1 + z.2 * W ω) ∂μ :=
    integral_map hW (by dsimp [f]; fun_prop)
  constructor
  · simpa only [hi] using hfint.integral_prod_left
  · calc
      _ = ∫ p, f p ∂μ.map (fun ω => ((A ω, D ω), W ω)) :=
        (integral_map hpair hf.stronglyMeasurable.aestronglyMeasurable).symm
      _ = ∫ p, f p ∂((μ.map (fun ω => (A ω, D ω))).prod (μ.map W)) := by rw [hlaw]
      _ = ∫ z : ℝ × ℝ, (∫ ω, ψ (z.1 + z.2 * W ω) ∂μ)
          ∂(μ.map (fun ω => (A ω, D ω))) := by
        rw [integral_prod f hfint]
        exact integral_congr_ae (Filter.Eventually.of_forall hi)

/-- A pointwise scalar comparison over an independent affine background can be
integrated against the background law. This is technical Fubini glue.

**Proof sketch.** Independence writes each expectation as an integral over the
common background law. Apply the integral triangle inequality and integrate the
scalar comparison, then pull the bound back to the original probability space. -/
theorem independent_affine_comparison_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A D U V : Ω → ℝ)
    (hAD : AEMeasurable (fun ω => (A ω, D ω)) μ)
    (hU : AEMeasurable U μ) (hV : AEMeasurable V μ)
    (hUAD : IndepFun U (fun ω => (A ω, D ω)) μ)
    (hVAD : IndepFun V (fun ω => (A ω, D ω)) μ)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (hψU : Integrable (fun ω => ψ (A ω + D ω * U ω)) μ)
    (hψV : Integrable (fun ω => ψ (A ω + D ω * V ω)) μ)
    (B : ℝ × ℝ → ℝ) (hB : Measurable B)
    (hBAD : Integrable (fun ω => B (A ω, D ω)) μ)
    (hscalar : ∀ z : ℝ × ℝ,
      |(∫ ω, ψ (z.1 + z.2 * U ω) ∂μ) -
        (∫ ω, ψ (z.1 + z.2 * V ω) ∂μ)| ≤ B z) :
    |(∫ ω, ψ (A ω + D ω * U ω) ∂μ) -
      (∫ ω, ψ (A ω + D ω * V ω) ∂μ)| ≤
      ∫ ω, B (A ω, D ω) ∂μ := by
  obtain ⟨hIU, eU⟩ :=
    independent_affine_integral A D U hAD hU hUAD ψ hψ hψU
  obtain ⟨hIV, eV⟩ :=
    independent_affine_integral A D V hAD hV hVAD ψ hψ hψV
  have hbound : Integrable B (μ.map (fun ω => (A ω, D ω))) :=
    (integrable_map_measure hB.aestronglyMeasurable hAD).mpr hBAD
  rw [eU, eV, ← integral_sub hIU hIV]
  calc
    _ ≤ ∫ z : ℝ × ℝ,
        |(∫ ω, ψ (z.1 + z.2 * U ω) ∂μ) -
          (∫ ω, ψ (z.1 + z.2 * V ω) ∂μ)|
          ∂(μ.map (fun ω => (A ω, D ω))) := abs_integral_le_integral_abs
    _ ≤ ∫ z : ℝ × ℝ, B z ∂(μ.map (fun ω => (A ω, D ω))) :=
      integral_mono_ae (hIU.sub hIV).abs hbound (Filter.Eventually.of_forall hscalar)
    _ = _ := integral_map hAD hB.aestronglyMeasurable

/-- Replacing an input independent of a shared affine background changes the
expected test by at most `3C/4` times the fourth moment of its random coefficient.
[OD14, §11.6, proof of the Basic Invariance Principle (11.29)]

**Proof sketch.** Factor each input's joint law with the background. Fubini
expresses the expectations over the same background law. Apply the scalar
replacement estimate at each background point and integrate its bound. -/
theorem independent_affine_replacement_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A D U V : Ω → ℝ)
    (hA : MemLp A 4 μ) (hD : MemLp D 4 μ)
    (hU : HasInvarianceMoments U μ) (hV : HasInvarianceMoments V μ)
    (hUAD : IndepFun U (fun ω => (A ω, D ω)) μ)
    (hVAD : IndepFun V (fun ω => (A ω, D ω)) μ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, |iteratedDeriv 4 ψ t| ≤ C)
    (hψU : Integrable (fun ω => ψ (A ω + D ω * U ω)) μ)
    (hψV : Integrable (fun ω => ψ (A ω + D ω * V ω)) μ) :
    |(∫ ω, ψ (A ω + D ω * U ω) ∂μ) -
      (∫ ω, ψ (A ω + D ω * V ω) ∂μ)| ≤
      (3 * C / 4) * (∫ ω, D ω ^ 4 ∂μ) := by
  have hAD :=
    hA.aestronglyMeasurable.aemeasurable.prodMk hD.aestronglyMeasurable.aemeasurable
  have hD4 : Integrable (fun ω => D ω ^ 4) μ := by
    simpa using Hypercontractivity.integrable_mul_pow_of_memLp
      (p := 4) (a := 4) (b := 0) hD hD (by omega)
  simpa only [integral_const_mul] using independent_affine_comparison_bound A D U V
    hAD hU.reasonable.memLp.aestronglyMeasurable.aemeasurable
    hV.reasonable.memLp.aestronglyMeasurable.aemeasurable hUAD hVAD
    ψ hψ.continuous hψU hψV (fun z : ℝ × ℝ => (3 * C / 4) * z.2 ^ 4)
    (by fun_prop) (hD4.const_mul (3 * C / 4))
    (fun z => affine_replacement_bound U V hU hV ψ hψ C hC0 hC z.1 z.2)

/-- Independent scalar inputs with matching first two moments satisfy a
third-order comparison over a common affine background.
[OD14, §11.5, Invariance Principle for Sums; Remark 11.66]

**Proof sketch.** Factor out the background law and apply scalar quadratic
Taylor replacement. Integrate the third absolute moment of the random coefficient. -/
theorem independent_affine_replacement_bound_c3
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A D U V : Ω → ℝ)
    (hAD : AEMeasurable (fun ω => (A ω, D ω)) μ)
    (hD : MemLp D 3 μ) (hU : MemLp U 3 μ) (hV : MemLp V 3 μ)
    (hmean : (∫ ω, U ω ∂μ) = ∫ ω, V ω ∂μ)
    (hsecond : (∫ ω, U ω ^ 2 ∂μ) = ∫ ω, V ω ^ 2 ∂μ)
    (hUAD : IndepFun U (fun ω => (A ω, D ω)) μ)
    (hVAD : IndepFun V (fun ω => (A ω, D ω)) μ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 3 ψ)
    (C : ℝ) (hC : ∀ t, |iteratedDeriv 3 ψ t| ≤ C)
    (hψU : Integrable (fun ω => ψ (A ω + D ω * U ω)) μ)
    (hψV : Integrable (fun ω => ψ (A ω + D ω * V ω)) μ) :
    |(∫ ω, ψ (A ω + D ω * U ω) ∂μ) -
      (∫ ω, ψ (A ω + D ω * V ω) ∂μ)| ≤
      (C / 6) * ((∫ ω, |U ω| ^ 3 ∂μ) + ∫ ω, |V ω| ^ 3 ∂μ) *
        (∫ ω, |D ω| ^ 3 ∂μ) := by
  let K := (C / 6) * ((∫ ω, |U ω| ^ 3 ∂μ) + ∫ ω, |V ω| ^ 3 ∂μ)
  have hD3 : Integrable (fun ω => |D ω| ^ 3) μ := by
    simpa only [Real.norm_eq_abs] using hD.integrable_norm_pow'
  simpa only [integral_const_mul] using independent_affine_comparison_bound A D U V
    hAD hU.aestronglyMeasurable.aemeasurable hV.aestronglyMeasurable.aemeasurable
    hUAD hVAD ψ hψ.continuous hψU hψV
    (fun z : ℝ × ℝ => K * |z.2| ^ 3) (by fun_prop) (hD3.const_mul K)
    (fun z => by
      calc
        _ ≤ (C / 6) * |z.2| ^ 3 *
            ((∫ ω, |U ω| ^ 3 ∂μ) + ∫ ω, |V ω| ^ 3 ∂μ) :=
          affine_replacement_bound_c3 U V hU hV hmean hsecond ψ hψ C hC z.1 z.2
        _ = _ := by dsimp [K]; ring)

/-- Replacing one coordinate between independent input families that agree on
the other coordinates changes the test expectation by at most
`(C/12) 9^(k+1) Infᵢ(F)²` for degree at most `k + 1`.
[OD14, §11.6, proof of the Basic Invariance Principle (11.29)]

**Proof sketch.** Split the polynomial into its coordinate-free part and the
coordinate times its derivative. Both parts agree between the two families.
Each input is independent of this common pair, so the affine replacement bound
gives `3C/4` times the derivative's fourth moment. General-input Bonami bounds
that moment by `9^k Infᵢ(F)²`. -/
theorem single_coordinate_replacement_bound
    {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost (k + 1))
    (i : Fin n) (X Y : Fin n → Ω → ℝ)
    (hIX : iIndepFun X μ) (hIY : iIndepFun Y μ)
    (hX : ∀ j, HasInvarianceMoments (X j) μ)
    (hY : ∀ j, HasInvarianceMoments (Y j) μ)
    (hXY : ∀ j, j ≠ i → X j = Y j)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, |iteratedDeriv 4 ψ t| ≤ C) :
    |(∫ ω, ψ (evalMultilinearRV F X ω) ∂μ) -
      (∫ ω, ψ (evalMultilinearRV F Y ω) ∂μ)| ≤
      (C / 12) * (9 : ℝ) ^ (k + 1) * (influence i F.eval) ^ 2 := by
  classical
  let A := evalMultilinearRV (Invariance.coordinateFree F i) X
  let D := evalMultilinearRV (Invariance.coordinateDerivative F i) X
  obtain ⟨hAeq, hDeq⟩ := Invariance.coordinate_parts_eq_of_off_coordinate F i X Y hXY
  change A = evalMultilinearRV (Invariance.coordinateFree F i) Y at hAeq
  change D = evalMultilinearRV (Invariance.coordinateDerivative F i) Y at hDeq
  have hsplitX : evalMultilinearRV F X = fun ω => A ω + D ω * X i ω := by
    funext ω
    simpa only [A, D, mul_comm] using Invariance.eval_coordinate_split F i X ω
  have hsplitY : evalMultilinearRV F Y = fun ω => A ω + D ω * Y i ω := by
    funext ω
    rw [Invariance.eval_coordinate_split, ← hAeq, ← hDeq]
    ring
  have hXm (j : Fin n) := (hX j).reasonable.memLp
  have hYm (j : Fin n) := (hY j).reasonable.memLp
  have hIndY : IndepFun (Y i) (fun ω => (A ω, D ω)) μ := by
    rw [hAeq, hDeq]
    exact Invariance.indep_coordinate_parts hIY
      (fun j => (hYm j).aestronglyMeasurable.aemeasurable) F i
  calc
    _ ≤ (3 * C / 4) * (∫ ω, D ω ^ 4 ∂μ) := by
      rw [hsplitX, hsplitY]
      apply independent_affine_replacement_bound A D (X i) (Y i)
        (evalMultilinearRV_memLp _ X μ hIX hXm)
        (evalMultilinearRV_memLp _ X μ hIX hXm) (hX i) (hY i)
        (Invariance.indep_coordinate_parts hIX
          (fun j => (hXm j).aestronglyMeasurable.aemeasurable) F i)
        hIndY ψ hψ C hC0 hC
      · simpa only [hsplitX] using integrable_test_of_memLp_four
          (evalMultilinearRV_memLp F X μ hIX hXm) ψ hψ C hC0 hC
      · simpa only [hsplitY] using integrable_test_of_memLp_four
          (evalMultilinearRV_memLp F Y μ hIY hYm) ψ hψ C hC0 hC
    _ ≤ (3 * C / 4) * ((9 : ℝ) ^ k * (influence i F.eval) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (invariance_coordinate_fourth_moment F hdegree i X hIX hX) (by positivity)
    _ = _ := by rw [pow_succ]; ring

end BooleanAnalysis.GaussianSpace
