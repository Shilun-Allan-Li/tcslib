/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Replacement
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Summing coordinate replacements

## Main definitions

* `Invariance.hybridIndex`: choose between two copies of each input coordinate.
* `Invariance.hybridInput`: replace the first coordinates of the left input by the right input.

## Main results

* `Invariance.hybridIndex_injective`: each hybrid selects distinct input coordinates.
* `Invariance.hybridInput_zero`: the initial hybrid is the left family.
* `Invariance.hybridInput_all`: the terminal hybrid is the right family.
* `Invariance.hybridInput_succ_off`: consecutive hybrids agree away from the replaced coordinate.
* `Invariance.hybrid_expectation_bound`: sum arbitrary coordinate replacement bounds.
* `Invariance.invariance_of_independent_pair`: the fourth-order replacement estimate.
* `Invariance.independent_input_coupling`: mutually independent copies of marginal laws.
* `Invariance.independent_polynomial_coupling`: copies preserving polynomial output laws.
* `Invariance.identDistrib_evalMultilinearRV`: transport polynomial output laws.
* `Invariance.identDistrib_of_independent_coordinates`: transport independent vectors by their laws.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, replacement argument proving (11.29).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace.Invariance

open ThresholdFunctions Hypercontractivity

/-- Choose the right input before position `r` and the left input from that
position onward. [OD14, §11.6, replacement sequence in the proof of (11.29)] -/
def hybridIndex {n : ℕ} (r : ℕ) (i : Fin n) : Fin n ⊕ Fin n :=
  if i.val < r then Sum.inr i else Sum.inl i

/-- The input family after replacing its first `r` left coordinates by their
right counterparts. [OD14, §11.6, replacement sequence in the proof of (11.29)] -/
def hybridInput {n : ℕ} {Ω : Type*}
    (Z : (Fin n ⊕ Fin n) → Ω → ℝ) (r : ℕ) : Fin n → Ω → ℝ :=
  fun i => Z (hybridIndex r i)

/-- Every hybrid selects distinct coordinates from the two input copies. -/
lemma hybridIndex_injective {n : ℕ} (r : ℕ) :
    Function.Injective (@hybridIndex n r) := by
  intro i j h
  unfold hybridIndex at h
  split_ifs at h <;> simp_all

/-- The initial hybrid is the left input family. -/
lemma hybridInput_zero {n : ℕ} {Ω : Type*}
    (Z : (Fin n ⊕ Fin n) → Ω → ℝ) :
    hybridInput Z 0 = fun i => Z (Sum.inl i) := by
  funext i
  simp [hybridInput, hybridIndex]

/-- The terminal hybrid is the right input family, including in dimension zero. -/
lemma hybridInput_all {n : ℕ} {Ω : Type*}
    (Z : (Fin n ⊕ Fin n) → Ω → ℝ) :
    hybridInput Z n = fun i => Z (Sum.inr i) := by
  funext i
  simp [hybridInput, hybridIndex, i.isLt]

/-- Consecutive hybrids agree on every coordinate other than the one being replaced. -/
lemma hybridInput_succ_off {n : ℕ} {Ω : Type*}
    (Z : (Fin n ⊕ Fin n) → Ω → ℝ) (i j : Fin n) (hji : j ≠ i) :
    hybridInput Z i.val j = hybridInput Z (i.val + 1) j := by
  have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
  have hlt : j.val < i.val ↔ j.val < i.val + 1 := by omega
  simp only [hybridInput, hybridIndex, hlt]

/-- Bounds for successive coordinate replacements sum to a bound for the two
endpoint expectations. [OD14, §11.6, replacement argument]

**Proof sketch.** Apply the triangle inequality along the finite hybrid sequence. -/
theorem hybrid_expectation_bound
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : MultilinearPolynomial n) (Z : (Fin n ⊕ Fin n) → Ω → ℝ)
    (ψ : ℝ → ℝ) (B : Fin n → ℝ)
    (hstep : ∀ i : Fin n,
      |(∫ ω, ψ (evalMultilinearRV F (hybridInput Z i.val) ω) ∂μ) -
        ∫ ω, ψ (evalMultilinearRV F (hybridInput Z (i.val + 1)) ω) ∂μ| ≤ B i) :
    |(∫ ω, ψ (evalMultilinearRV F (fun i => Z (Sum.inl i)) ω) ∂μ) -
      ∫ ω, ψ (evalMultilinearRV F (fun i => Z (Sum.inr i)) ω) ∂μ| ≤ ∑ i, B i := by
  let P : ℕ → ℝ := fun r => ∫ ω, ψ (evalMultilinearRV F (hybridInput Z r) ω) ∂μ
  calc
    _ = dist (P 0) (P n) := by
      simp only [P, hybridInput_zero, hybridInput_all, Real.dist_eq]
    _ ≤ ∑ r ∈ Finset.range n, dist (P r) (P (r + 1)) :=
      dist_le_range_sum_dist P n
    _ = ∑ i : Fin n, dist (P i.val) (P (i.val + 1)) :=
      (Fin.sum_univ_eq_sum_range (fun r => dist (P r) (P (r + 1))) n).symm
    _ ≤ ∑ i : Fin n, B i :=
      Finset.sum_le_sum fun i _ => by simpa only [P, Real.dist_eq] using hstep i

/-- The invariance estimate for two input families drawn from a single mutually
independent family containing both copies of the coordinates.
[OD14, §11.6, replacement argument proving (11.29)]

**Proof sketch.** A degree-zero polynomial is constant. Otherwise, replace
coordinates in index order. Each hybrid is a selection of distinct independent
inputs, and consecutive hybrids differ at one coordinate. Apply the checked
single-coordinate estimate and sum using the triangle inequality. -/
theorem invariance_of_independent_pair
    {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost k)
    (Z : (Fin n ⊕ Fin n) → Ω → ℝ)
    (hIZ : iIndepFun Z μ) (hZ : ∀ i, HasInvarianceMoments (Z i) μ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, |iteratedDeriv 4 ψ t| ≤ C) :
    |(∫ ω, ψ (evalMultilinearRV F (fun i => Z (Sum.inl i)) ω) ∂μ) -
      (∫ ω, ψ (evalMultilinearRV F (fun i => Z (Sum.inr i)) ω) ∂μ)| ≤
      (C / 12) * (9 : ℝ) ^ k * ∑ i : Fin n, (influence i F.eval) ^ 2 := by
  classical
  cases k with
  | zero =>
      have hconst (W : Fin n → Ω → ℝ) (ω : Ω) : evalMultilinearRV F W ω = F ∅ := by
        simpa using MultilinearMoments.eval_supported F W ∅
          (fun T hT => hdegree T (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr
            (by simpa only [Finset.subset_empty] using hT)))) ω
      simp only [hconst, sub_self, abs_zero]
      positivity
  | succ k =>
      have hI (r : ℕ) : iIndepFun (hybridInput Z r) μ :=
        iIndepFun.precomp (f := Z) (g := hybridIndex r) (hybridIndex_injective r) hIZ
      calc
        _ ≤ ∑ i : Fin n,
            (C / 12) * (9 : ℝ) ^ (k + 1) * (influence i F.eval) ^ 2 := by
          apply hybrid_expectation_bound
          intro i
          exact single_coordinate_replacement_bound F hdegree i
            (hybridInput Z i.val) (hybridInput Z (i.val + 1))
            (hI i.val) (hI (i.val + 1))
            (fun j => hZ (hybridIndex i.val j))
            (fun j => hZ (hybridIndex (i.val + 1) j))
            (fun j hji => hybridInput_succ_off Z i j hji) ψ hψ C hC0 hC
        _ = _ := by rw [Finset.mul_sum]

/-- Two finite real input families admit mutually independent copies preserving
all coordinate laws. This is the independent coupling in [OD14, §11.6, proof of (11.29)].

**Proof sketch.** Take the product of all coordinate marginal laws. Its evaluation
maps are independent and each has its prescribed marginal distribution. -/
theorem independent_input_coupling
    {ι Ω Ξ : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ι → Ω → ℝ) (Y : ι → Ξ → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ) (hY : ∀ i, AEMeasurable (Y i) ν) :
    ∃ (κ : Measure ((ι ⊕ ι) → ℝ)) (_ : IsProbabilityMeasure κ)
      (Z : (ι ⊕ ι) → ((ι ⊕ ι) → ℝ) → ℝ),
      iIndepFun Z κ ∧ (∀ i, IdentDistrib (X i) (Z (Sum.inl i)) μ κ) ∧
        (∀ i, IdentDistrib (Y i) (Z (Sum.inr i)) ν κ) := by
  let laws : ι ⊕ ι → Measure ℝ :=
    Sum.elim (fun i => μ.map (X i)) (fun i => ν.map (Y i))
  haveI (a : ι ⊕ ι) : IsProbabilityMeasure (laws a) := by
    cases a with
    | inl i => exact Measure.isProbabilityMeasure_map (hX i)
    | inr i => exact Measure.isProbabilityMeasure_map (hY i)
  refine ⟨Measure.pi laws, inferInstance, fun a z => z a, ?_, ?_, ?_⟩
  · exact iIndepFun_pi (μ := laws) (X := fun _ => id) (fun _ => aemeasurable_id)
  · intro i
    exact ⟨hX i, (measurable_pi_apply _).aemeasurable,
      (measurePreserving_eval laws (Sum.inl i)).map_eq.symm⟩
  · intro i
    exact ⟨hY i, (measurable_pi_apply _).aemeasurable,
      (measurePreserving_eval laws (Sum.inr i)).map_eq.symm⟩

/-- Independent finite real vectors with the same coordinate laws have the same
joint law. This is the independent-coupling transport used in
[OD14, §11.6, proof of (11.29)].

**Proof sketch.** Each joint law is the product of its marginal laws.
The coordinate law equalities identify the factors in those products. -/
theorem identDistrib_of_independent_coordinates
    {ι Ω Ξ : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ι → Ω → ℝ) (Y : ι → Ξ → ℝ)
    (hIX : iIndepFun X μ) (hIY : iIndepFun Y ν)
    (hXY : ∀ i, IdentDistrib (X i) (Y i) μ ν) :
    IdentDistrib (fun ω i => X i ω) (fun ω i => Y i ω) μ ν := by
  refine
    { aemeasurable_fst := aemeasurable_pi_lambda _ (fun i => (hXY i).aemeasurable_fst)
      aemeasurable_snd := aemeasurable_pi_lambda _ (fun i => (hXY i).aemeasurable_snd)
      map_eq := ?_ }
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hXY i).aemeasurable_fst)).mp hIX,
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hXY i).aemeasurable_snd)).mp hIY]
  congr 1
  funext i
  exact (hXY i).map_eq

/-- Polynomial evaluations of independent input families with the same marginal
laws have the same distribution. [OD14, §11.6, independent coupling argument] -/
theorem identDistrib_evalMultilinearRV
    {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : MultilinearPolynomial n) (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ)
    (hIX : iIndepFun X μ) (hIY : iIndepFun Y ν)
    (hXY : ∀ i, IdentDistrib (X i) (Y i) μ ν) :
    IdentDistrib (evalMultilinearRV F X) (evalMultilinearRV F Y) μ ν := by
  exact (identDistrib_of_independent_coordinates X Y hIX hIY hXY).comp
    (show Measurable (fun z : Fin n → ℝ =>
      ∑ S : Finset (Fin n), F S * ∏ i ∈ S, z i) by fun_prop)

/-- Independent copies preserve both marginal input laws and the two polynomial
output laws. [OD14, §11.6, coupling in the invariance proof] -/
theorem independent_polynomial_coupling
    {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : MultilinearPolynomial n) (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ)
    (hIX : iIndepFun X μ) (hIY : iIndepFun Y ν)
    (hX : ∀ i, AEMeasurable (X i) μ) (hY : ∀ i, AEMeasurable (Y i) ν) :
    ∃ (κ : Measure ((Fin n ⊕ Fin n) → ℝ)) (_ : IsProbabilityMeasure κ)
      (Z : (Fin n ⊕ Fin n) → ((Fin n ⊕ Fin n) → ℝ) → ℝ),
      iIndepFun Z κ ∧ (∀ i, IdentDistrib (X i) (Z (Sum.inl i)) μ κ) ∧
        (∀ i, IdentDistrib (Y i) (Z (Sum.inr i)) ν κ) ∧
        IdentDistrib (evalMultilinearRV F X) (evalMultilinearRV F (fun i => Z (Sum.inl i))) μ κ ∧
        IdentDistrib (evalMultilinearRV F Y) (evalMultilinearRV F (fun i => Z (Sum.inr i))) ν κ := by
  obtain ⟨κ, hκ, Z, hIZ, hL, hR⟩ := independent_input_coupling X Y hX hY
  letI := hκ
  refine ⟨κ, hκ, Z, hIZ, hL, hR, ?_, ?_⟩
  · exact identDistrib_evalMultilinearRV F X (fun i => Z (Sum.inl i))
      hIX (iIndepFun.precomp (f := Z) (g := Sum.inl) Sum.inl_injective hIZ) hL
  · exact identDistrib_evalMultilinearRV F Y (fun i => Z (Sum.inr i))
      hIY (iIndepFun.precomp (f := Z) (g := Sum.inr) Sum.inr_injective hIZ) hR

end BooleanAnalysis.GaussianSpace.Invariance
