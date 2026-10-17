/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TCSlib.BooleanAnalysis.GaussianSpace.Inputs
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Coordinates
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Moments
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Replacement
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Sequence
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Smoothing
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Taylor
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourth-order invariance for independent multilinear inputs

## Contents

* `Coordinates`: coordinate-free and derivative polynomial parts and their independence.
* `Moments`: the polynomial and coordinate fourth-moment bounds from general-input Bonami.
* `Taylor`: the cubic moment identities and scalar replacement estimate.
* `Replacement`: the single-coordinate Taylor replacement bound.
* `Sequence`: replacement telescoping and transport between independent input laws.
* `Smoothing`: quantitative interval averaging and Lipschitz-test comparison.

## Main definitions

No polynomial representation, evaluation, variance, or influence is introduced here.
We use `ThresholdFunctions.MultilinearPolynomial`, `Hypercontractivity.evalMultilinearRV`,
and the existing cube variance and influence of `F.eval`. The existing coefficient
identity `MultilinearPolynomial.fourierCoeff_eval` identifies these with Definition 11.63.
`HasInvarianceMoments` packages Hypothesis 11.65 in `Inputs`.

## Main results

* `basic_invariance_principle`: the exact fourth-order estimate (11.29).
* `invariance_small_influences`: the variance-normalized estimate of Corollary 11.67.
* `invariance_lipschitz`: the universal Lipschitz-test estimate of Corollary 11.68.

Separate sample spaces are allowed: a product
coupling gives the source's mutually independent replacement family without imposing
an irrelevant joint law on `X` and `Y`. The existing `IsBReasonable` and
`evalMultilinearRV_memLp` infrastructure ensures finite fourth moments; a `C⁴` test with
bounded fourth derivative has at most quartic growth, so the displayed expectations exist.

This is the general-input `C⁴` theorem. The `C³` Boolean-to-Gaussian theorem already
present in atlas-lean is recorded as an external dependency, not restated here.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, Basic Invariance Principle (11.29),
  Hypothesis 11.65, and Corollaries 11.67–11.68.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions Hypercontractivity

/-- A degree-`k` multilinear polynomial has nearly the same expectation under a
`C⁴` test on two independent input families satisfying Hypothesis 11.65. The error
is `(C/12) 9^k ∑ᵢ Infᵢ(F)²`, where `C` bounds the fourth derivative.
[OD14, §11.6, Basic Invariance Principle, equation (11.29)]

**Proof sketch.** Couple the families independently and replace the coordinates one
at a time. Expand the test through order three in the coordinate being replaced.
The first three moments agree, so these terms cancel in expectation. Bound each
fourth-order remainder with the existing general-input Bonami inequality applied
to the part of the polynomial containing that coordinate. Sum the resulting
`(C/12) 9^k Infᵢ(F)²` bounds along the replacement sequence. -/
theorem basic_invariance_principle {n k : ℕ}
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost k)
    (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ)
    (hIX : iIndepFun X μ) (hIY : iIndepFun Y ν)
    (hX : ∀ i, HasInvarianceMoments (X i) μ)
    (hY : ∀ i, HasInvarianceMoments (Y i) ν)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, |iteratedDeriv 4 ψ t| ≤ C) :
    |(∫ ω, ψ (evalMultilinearRV F X ω) ∂μ) -
      (∫ ω, ψ (evalMultilinearRV F Y ω) ∂ν)| ≤
      (C / 12) * (9 : ℝ) ^ k * ∑ i : Fin n, (influence i F.eval) ^ 2 := by
  classical
  let laws : Fin n ⊕ Fin n → Measure ℝ :=
    Sum.elim (fun i => μ.map (X i)) (fun i => ν.map (Y i))
  haveI (a : Fin n ⊕ Fin n) : IsProbabilityMeasure (laws a) := by
    cases a with
    | inl i =>
        exact Measure.isProbabilityMeasure_map
          (hX i).reasonable.memLp.aestronglyMeasurable.aemeasurable
    | inr i =>
        exact Measure.isProbabilityMeasure_map
          (hY i).reasonable.memLp.aestronglyMeasurable.aemeasurable
  let ρ := Measure.pi laws
  let Z : (Fin n ⊕ Fin n) → ((Fin n ⊕ Fin n) → ℝ) → ℝ := fun a z => z a
  have hIZ : iIndepFun Z ρ :=
    iIndepFun_pi (μ := laws) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hL (i : Fin n) : IdentDistrib (X i) (Z (Sum.inl i)) μ ρ :=
    { aemeasurable_fst := (hX i).reasonable.memLp.aestronglyMeasurable.aemeasurable
      aemeasurable_snd := (measurable_pi_apply _).aemeasurable
      map_eq := (measurePreserving_eval laws (Sum.inl i)).map_eq.symm }
  have hR (i : Fin n) : IdentDistrib (Y i) (Z (Sum.inr i)) ν ρ :=
    { aemeasurable_fst := (hY i).reasonable.memLp.aestronglyMeasurable.aemeasurable
      aemeasurable_snd := (measurable_pi_apply _).aemeasurable
      map_eq := (measurePreserving_eval laws (Sum.inr i)).map_eq.symm }
  have hZ (a : Fin n ⊕ Fin n) : HasInvarianceMoments (Z a) ρ := by
    cases a with
    | inl i => exact (hX i).identDistrib (hL i)
    | inr i => exact (hY i).identDistrib (hR i)
  have hXL := Invariance.identDistrib_of_independent_coordinates X (fun i => Z (Sum.inl i))
    hIX (iIndepFun.precomp (f := Z) (g := Sum.inl) Sum.inl_injective hIZ) hL
  have hYR := Invariance.identDistrib_of_independent_coordinates Y (fun i => Z (Sum.inr i))
    hIY (iIndepFun.precomp (f := Z) (g := Sum.inr) Sum.inr_injective hIZ) hR
  let f : (Fin n → ℝ) → ℝ := fun z =>
    ψ (evalMultilinearRV F (fun i z => z i) z)
  have hf : Measurable f := by
    apply hψ.continuous.measurable.comp
    change Measurable (fun z : Fin n → ℝ =>
      ∑ S : Finset (Fin n), F S * ∏ i ∈ S, z i)
    fun_prop
  have eX : (∫ ω, ψ (evalMultilinearRV F X ω) ∂μ) =
      ∫ z, ψ (evalMultilinearRV F (fun i => Z (Sum.inl i)) z) ∂ρ :=
    (hXL.comp hf).integral_eq
  have eY : (∫ ω, ψ (evalMultilinearRV F Y ω) ∂ν) =
      ∫ z, ψ (evalMultilinearRV F (fun i => Z (Sum.inr i)) z) ∂ρ :=
    (hYR.comp hf).integral_eq
  rw [eX, eY]
  exact Invariance.invariance_of_independent_pair F hdegree Z hIZ hZ ψ hψ C hC0 hC

/-- With variance at most one and all influences at most `ε`, the fourth-order
invariance error is at most `(C/12) k 9^k ε`. [OD14, Cor. 11.67]

**Proof sketch.** Apply the Basic Invariance Principle, then use
`∑ᵢ Infᵢ² ≤ ε ∑ᵢ Infᵢ ≤ ε k Var(F)`. The existing Fourier coefficient and
degree identities on `F.eval` justify the last inequality. -/
theorem invariance_small_influences {n k : ℕ}
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost k)
    (hvar : cubeVariance F.eval ≤ 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hinf : ∀ i, influence i F.eval ≤ ε)
    (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ)
    (hIX : iIndepFun X μ) (hIY : iIndepFun Y ν)
    (hX : ∀ i, HasInvarianceMoments (X i) μ)
    (hY : ∀ i, HasInvarianceMoments (Y i) ν)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, |iteratedDeriv 4 ψ t| ≤ C) :
    |(∫ ω, ψ (evalMultilinearRV F X ω) ∂μ) -
      (∫ ω, ψ (evalMultilinearRV F Y ω) ∂ν)| ≤
      (C / 12) * (k : ℝ) * (9 : ℝ) ^ k * ε := by
  calc
    _ ≤ (C / 12) * (9 : ℝ) ^ k * ∑ i : Fin n, (influence i F.eval) ^ 2 :=
      basic_invariance_principle F hdegree X Y hIX hIY hX hY ψ hψ C hC0 hC
    _ ≤ (C / 12) * (9 : ℝ) ^ k * ((k : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left
        (sum_sq_influences_le_degree_mul F.eval (F.has_degree_at_most_eval hdegree)
          hvar ε hε hinf) (by positivity)
    _ = _ := by ring

/-- The degree factor in the smooth invariance bound is at most `16^k`.
[OD14, Cor. 11.68 (proof), explicit numerical estimate]

**Proof sketch.** Check degrees zero and one directly. Starting at degree two,
increasing the degree multiplies the factor by at most `16`. -/
private theorem degree_mul_nine_pow_le_sixteen_pow (k : ℕ) :
    (k : ℝ) * (9 : ℝ) ^ k ≤ (16 : ℝ) ^ k := by
  rcases k with _ | _ | k
  · norm_num
  · norm_num
  · suffices h : ∀ m : ℕ, ((m + 2 : ℕ) : ℝ) * (9 : ℝ) ^ (m + 2) ≤
        (16 : ℝ) ^ (m + 2) by exact h k
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      have hstep : ((m + 1 + 2 : ℕ) : ℝ) * 9 ≤ 16 * ((m + 2 : ℕ) : ℝ) := by
        push_cast
        nlinarith
      calc
        ((m + 1 + 2 : ℕ) : ℝ) * (9 : ℝ) ^ (m + 1 + 2) =
            (((m + 1 + 2 : ℕ) : ℝ) * 9) * (9 : ℝ) ^ (m + 2) := by
          rw [show m + 1 + 2 = (m + 2) + 1 by omega, pow_succ]
          ring
        _ ≤ (16 * ((m + 2 : ℕ) : ℝ)) * (9 : ℝ) ^ (m + 2) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
        _ ≤ 16 * (16 : ℝ) ^ (m + 2) := by
          nlinarith [ih]
        _ = (16 : ℝ) ^ (m + 1 + 2) := by
          rw [show m + 1 + 2 = (m + 2) + 1 by omega, pow_succ]
          ring

/-- The fourth root of the smooth invariance scale is at most `2^k` times the fourth
root of the influence bound. [OD14, Cor. 11.68 (proof), explicit numerical estimate]

**Proof sketch.** Use monotonicity of real fourth roots and `k 9^k ≤ 16^k`, then
factor the fourth root of `16^k ε`. -/
private theorem invariance_quarter_power_le (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ((k : ℝ) * (9 : ℝ) ^ k * ε) ^ (1 / 4 : ℝ) ≤
      (2 : ℝ) ^ k * ε ^ (1 / 4 : ℝ) := by
  calc
    _ ≤ ((16 : ℝ) ^ k * ε) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_right (degree_mul_nine_pow_le_sixteen_pow k) hε)
        (by norm_num)
    _ = (2 : ℝ) ^ k * ε ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow (by positivity) hε,
        ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 16) _ k]
      have hroot : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
        simpa only [one_div] using
          Real.pow_rpow_inv_natCast (x := (2 : ℝ)) (n := 4) (by norm_num) (by norm_num)
      rw [hroot]

/-- There is a universal constant bounding the invariance error for a `c`-Lipschitz
test by `K c 2^k ε^(1/4)`, for variance at most one and influences at most `ε`.
[OD14, Cor. 11.68]
The constant is quantified before all dimensions, input laws, polynomials, tests,
and Lipschitz constants, making the source's `O(c)` dependence explicit.

**Proof sketch.** Four successive Mathlib interval averages give a `C⁴` test with
uniform error at most `4cη` and fourth derivative at most `8c/η³`. Apply Corollary
11.67, then the general smooth-to-Lipschitz expectation comparison at scale
`η = (k 9^k ε)^(1/4)`. The estimate `k 9^k ≤ 16^k` bounds the fourth root by
`2^k ε^(1/4)`. Zero error scale is handled by letting `η` decrease to zero.
This interval-average adaptation gives the explicit universal constant `K = 16`. -/
theorem invariance_lipschitz :
    ∃ K : ℝ, 0 < K ∧ ∀ {n k : ℕ}
      {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
      (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (F : MultilinearPolynomial n),
      F.HasDegreeAtMost k → cubeVariance F.eval ≤ 1 →
      ∀ (ε : ℝ), 0 ≤ ε → (∀ i, influence i F.eval ≤ ε) →
      ∀ (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ),
      iIndepFun X μ → iIndepFun Y ν →
      (∀ i, HasInvarianceMoments (X i) μ) →
      (∀ i, HasInvarianceMoments (Y i) ν) →
      ∀ (c : ℝ≥0) (ψ : ℝ → ℝ), LipschitzWith c ψ →
        |(∫ ω, ψ (evalMultilinearRV F X ω) ∂μ) -
          (∫ ω, ψ (evalMultilinearRV F Y ω) ∂ν)| ≤
          K * (c : ℝ) * (2 : ℝ) ^ k * ε ^ (1 / 4 : ℝ) := by
  refine ⟨16, by norm_num, ?_⟩
  intro n k Ω Ξ _ _ μ ν _ _ F hdegree hvar ε hε hinf X Y hIX hIY hX hY c ψ hψ
  have hB : 0 ≤ (k : ℝ) * (9 : ℝ) ^ k * ε := by positivity
  have hcomparison (φ : ℝ → ℝ) (hφ : ContDiff ℝ 4 φ)
      (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t, |iteratedDeriv 4 φ t| ≤ C) :
      |(∫ ω, φ (evalMultilinearRV F X ω) ∂μ) -
        ∫ ω, φ (evalMultilinearRV F Y ω) ∂ν| ≤
        C * ((k : ℝ) * (9 : ℝ) ^ k * ε) := by
    calc
      _ ≤ (C / 12) * (k : ℝ) * (9 : ℝ) ^ k * ε :=
        invariance_small_influences F hdegree hvar ε hε hinf X Y hIX hIY hX hY φ hφ C hC0 hC
      _ = (C / 12) * ((k : ℝ) * (9 : ℝ) ^ k * ε) := by ring
      _ ≤ C * ((k : ℝ) * (9 : ℝ) ^ k * ε) :=
        mul_le_mul_of_nonneg_right (by linarith) hB
  calc
    _ ≤ 16 * (c : ℝ) * ((k : ℝ) * (9 : ℝ) ^ k * ε) ^ (1 / 4 : ℝ) :=
      Invariance.lipschitz_expectation_bound_of_fourth_derivative
        (evalMultilinearRV_memLp F X μ hIX (fun i => (hX i).reasonable.memLp))
        (evalMultilinearRV_memLp F Y ν hIY (fun i => (hY i).reasonable.memLp))
        _ hB hcomparison c ψ hψ
    _ ≤ 16 * (c : ℝ) * ((2 : ℝ) ^ k * ε ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (invariance_quarter_power_le k hε) (by positivity)
    _ = _ := by ring

end BooleanAnalysis.GaussianSpace
