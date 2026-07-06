/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Total Variation Distance

## Main results

- `tvDistance_eq_tvDistanceSup`: The total-variation-mass definition agrees with the supremum-over-events definition.
- `abs_measureReal_sub_le_tvDistance`: The total variation distance bounds the probability gap of every measurable event.
- `tvDistance_nonneg`: Total variation distance is nonnegative.
- `tvDistanceSup_eq_half_sum`: On a finite measurable space, total variation distance is half the `ℓ¹` distance between the singleton masses.
- `tvDistance_eq_half_sum`: On a finite measurable space, total variation distance is half the `ℓ¹` distance between the singleton masses.
- `tvDistance_bool_eq_abs_true`: On `Bool`, total variation distance is the absolute singleton-mass gap at `true`.
- `tvDistance_prod_le`: The total variation distance between product distributions is bounded by the sum of the total variation distances between their marginals.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

open MeasureTheory

namespace CommunicationComplexity

/-- The signed difference between two probability measures, represented as measures with
`IsProbabilityMeasure` instances. -/
noncomputable def signedMeasureDiff {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : SignedMeasure Ω :=
  μ.toSignedMeasure - ν.toSignedMeasure

/-- Total variation distance between probability measures, defined using the total variation of
the signed measure `μ - ν`. -/
noncomputable def tvDistance {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ

/-- Total variation distance between probability measures, defined as the supremum over
measurable events. -/
noncomputable def tvDistanceSup {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  sSup (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
    |μ.real (S : Set Ω) - ν.real (S : Set Ω)|)

namespace TVDistance

private lemma signedMeasure_apply_eq_posPart_sub_negPart
    {Ω : Type*} [MeasurableSpace Ω] (s : SignedMeasure Ω)
    {S : Set Ω} (hS : MeasurableSet S) :
    s S =
      s.toJordanDecomposition.posPart.real S -
        s.toJordanDecomposition.negPart.real S := by
  conv_lhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition s]
  rw [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hS]

private lemma signedMeasureDiff_univ
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    signedMeasureDiff μ ν Set.univ = 0 := by
  rw [signedMeasureDiff, Measure.toSignedMeasure_sub_apply MeasurableSet.univ]
  simp

private lemma jordan_posPart_real_univ_eq_negPart_real_univ
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (signedMeasureDiff μ ν).toJordanDecomposition.posPart.real Set.univ =
      (signedMeasureDiff μ ν).toJordanDecomposition.negPart.real Set.univ := by
  have h := signedMeasure_apply_eq_posPart_sub_negPart (signedMeasureDiff μ ν) MeasurableSet.univ
  rw [signedMeasureDiff_univ μ ν] at h
  linarith

private lemma totalVariation_real_univ
    {Ω : Type*} [MeasurableSpace Ω] (s : SignedMeasure Ω) :
    s.totalVariation.real Set.univ =
      s.toJordanDecomposition.posPart.real Set.univ +
        s.toJordanDecomposition.negPart.real Set.univ := by
  rw [SignedMeasure.totalVariation, measureReal_add_apply]

private lemma half_totalVariation_real_univ_eq_posPart_real_univ
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ =
      (signedMeasureDiff μ ν).toJordanDecomposition.posPart.real Set.univ := by
  rw [totalVariation_real_univ]
  rw [jordan_posPart_real_univ_eq_negPart_real_univ μ ν]
  ring

private lemma event_abs_signedMeasureDiff_le_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : {S : Set Ω // MeasurableSet S}) :
    |signedMeasureDiff μ ν (S : Set Ω)| ≤
      (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  let P := (signedMeasureDiff μ ν).toJordanDecomposition.posPart
  let N := (signedMeasureDiff μ ν).toJordanDecomposition.negPart
  have hPN : P.real Set.univ = N.real Set.univ := by
    simpa [P, N] using jordan_posPart_real_univ_eq_negPart_real_univ μ ν
  have hPmono : P.real (S : Set Ω) ≤ P.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hNmono : N.real (S : Set Ω) ≤ N.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hPnonneg : 0 ≤ P.real (S : Set Ω) := measureReal_nonneg
  have hNnonneg : 0 ≤ N.real (S : Set Ω) := measureReal_nonneg
  have hbound :
      |P.real (S : Set Ω) - N.real (S : Set Ω)| ≤ P.real Set.univ := by
    rw [abs_le]
    constructor <;> linarith
  rw [half_totalVariation_real_univ_eq_posPart_real_univ μ ν]
  rw [signedMeasure_apply_eq_posPart_sub_negPart (signedMeasureDiff μ ν) S.property]
  simpa [P, N] using hbound

private lemma event_abs_measureReal_sub_le_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : {S : Set Ω // MeasurableSet S}) :
    |μ.real (S : Set Ω) - ν.real (S : Set Ω)| ≤
      (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  rw [← Measure.toSignedMeasure_sub_apply S.property]
  simpa [signedMeasureDiff] using event_abs_signedMeasureDiff_le_half_totalVariation μ ν S

private lemma exists_event_abs_signedMeasureDiff_eq_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ S : {S : Set Ω // MeasurableSet S},
      |signedMeasureDiff μ ν (S : Set Ω)| =
        (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  let s := signedMeasureDiff μ ν
  obtain ⟨S, hS, -, -, hPzero, hNzero⟩ :=
    s.toJordanDecomposition.exists_compl_positive_negative
  refine ⟨⟨Sᶜ, hS.compl⟩, ?_⟩
  let P := s.toJordanDecomposition.posPart
  let N := s.toJordanDecomposition.negPart
  have hPzero_real : P.real S = 0 := by
    rw [measureReal_def, show P S = 0 by simpa [P] using hPzero, ENNReal.toReal_zero]
  have hPcompl : P.real Sᶜ = P.real Set.univ := by
    rw [measureReal_compl hS, hPzero_real]
    ring
  have hNcompl : N.real Sᶜ = 0 := by
    rw [measureReal_def, hNzero, ENNReal.toReal_zero]
  have hnonneg : 0 ≤ P.real Set.univ := measureReal_nonneg
  rw [signedMeasure_apply_eq_posPart_sub_negPart s hS.compl]
  rw [half_totalVariation_real_univ_eq_posPart_real_univ μ ν]
  simp [s, P, N, hPcompl, hNcompl, abs_of_nonneg hnonneg]

private lemma exists_event_abs_measureReal_sub_eq_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ S : {S : Set Ω // MeasurableSet S},
      |μ.real (S : Set Ω) - ν.real (S : Set Ω)| =
        (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  obtain ⟨S, hS⟩ := exists_event_abs_signedMeasureDiff_eq_half_totalVariation μ ν
  refine ⟨S, ?_⟩
  rw [← Measure.toSignedMeasure_sub_apply S.property]
  simpa [signedMeasureDiff] using hS

open Classical in
/-- The total-variation-mass definition agrees with the supremum-over-events definition. -/
theorem tvDistance_eq_tvDistanceSup
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDistance μ ν = tvDistanceSup μ ν := by
  let rhs : ℝ := (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ
  have hset_le (S : {S : Set Ω // MeasurableSet S}) :
      |μ.real (S : Set Ω) - ν.real (S : Set Ω)| ≤ rhs := by
    simpa [rhs] using event_abs_measureReal_sub_le_half_totalVariation μ ν S
  have hrhs_nonneg : 0 ≤ rhs := by
    dsimp [rhs]
    positivity
  have hupper : tvDistanceSup μ ν ≤ rhs := by
    rw [tvDistanceSup]
    exact Real.sSup_le (by rintro _ ⟨S, rfl⟩; exact hset_le S) hrhs_nonneg
  obtain ⟨Smax, hSmax⟩ := exists_event_abs_measureReal_sub_eq_half_totalVariation μ ν
  have hbdd :
      BddAbove (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |μ.real (S : Set Ω) - ν.real (S : Set Ω)|) := by
    exact ⟨rhs, by rintro _ ⟨S, rfl⟩; exact hset_le S⟩
  have hlower : rhs ≤ tvDistanceSup μ ν := by
    rw [tvDistanceSup]
    dsimp [rhs]
    rw [← hSmax]
    exact le_csSup hbdd (Set.mem_range_self Smax)
  rw [tvDistance]
  exact le_antisymm (by simpa [rhs] using hlower) (by simpa [rhs] using hupper)

/-- The total variation distance bounds the probability gap of every measurable event. -/
theorem abs_measureReal_sub_le_tvDistance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : {S : Set Ω // MeasurableSet S}) :
    |μ.real (S : Set Ω) - ν.real (S : Set Ω)| ≤
      tvDistance μ ν := by
  rw [tvDistance]
  exact event_abs_measureReal_sub_le_half_totalVariation μ ν S

/-- Total variation distance is nonnegative. -/
theorem tvDistance_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ tvDistance μ ν := by
  rw [tvDistance]
  positivity

open Classical in
private lemma sum_indicator_le_sum_posPart
    {α : Type*} [Fintype α] (a : α → ℝ) (S : Set α) :
    (∑ x : α, if x ∈ S then a x else 0) ≤
      ∑ x : α, if 0 ≤ a x then a x else 0 := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ S
  · by_cases ha : 0 ≤ a x
    · simp [hx, ha]
    · simp [hx, ha, le_of_not_ge ha]
  · by_cases ha : 0 ≤ a x <;> simp [hx, ha]

open Classical in
private lemma sum_posPart_eq_half_sum_abs
    {α : Type*} [Fintype α] (a : α → ℝ)
    (hsum : ∑ x : α, a x = 0) :
    (∑ x : α, if 0 ≤ a x then a x else 0) =
      (1 / 2 : ℝ) * ∑ x : α, |a x| := by
  have habs :
      (∑ x : α, |a x|) =
        ∑ x : α, ((2 : ℝ) * (if 0 ≤ a x then a x else 0) - a x) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases ha : 0 ≤ a x
    · simp [ha, abs_of_nonneg ha]
      ring
    · have hle : a x ≤ 0 := le_of_not_ge ha
      simp [ha, abs_of_nonpos hle]
  have hsum_abs :
      (∑ x : α, |a x|) =
        (2 : ℝ) * ∑ x : α, if 0 ≤ a x then a x else 0 := by
    rw [habs, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    ring
  linarith

open Classical in
private lemma abs_sum_indicator_le_half_sum_abs
    {α : Type*} [Fintype α] (a : α → ℝ)
    (hsum : ∑ x : α, a x = 0) (S : Set α) :
    |∑ x : α, if x ∈ S then a x else 0| ≤
      (1 / 2 : ℝ) * ∑ x : α, |a x| := by
  let posPart : ℝ := ∑ x : α, if 0 ≤ a x then a x else 0
  have hposPart : posPart = (1 / 2 : ℝ) * ∑ x : α, |a x| := by
    simp [posPart, sum_posPart_eq_half_sum_abs a hsum]
  have hupper :
      (∑ x : α, if x ∈ S then a x else 0) ≤ posPart := by
    simpa [posPart] using sum_indicator_le_sum_posPart a S
  have hcomplUpper :
      (∑ x : α, if x ∈ Sᶜ then a x else 0) ≤ posPart := by
    simpa [posPart] using sum_indicator_le_sum_posPart a Sᶜ
  have hdecomp :
      (∑ x : α, a x) =
        (∑ x : α, if x ∈ S then a x else 0) +
          ∑ x : α, if x ∈ Sᶜ then a x else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ S <;> simp [hx]
  have hlower :
      -posPart ≤ ∑ x : α, if x ∈ S then a x else 0 := by
    linarith
  rw [hposPart] at hupper hlower
  exact abs_le.mpr ⟨hlower, hupper⟩

open Classical in
private lemma abs_sum_pos_indicator_eq_half_sum_abs
    {α : Type*} [Fintype α] (a : α → ℝ)
    (hsum : ∑ x : α, a x = 0) :
    |∑ x : α, if 0 ≤ a x then a x else 0| =
      (1 / 2 : ℝ) * ∑ x : α, |a x| := by
  have hnonneg : 0 ≤ ∑ x : α, if 0 ≤ a x then a x else 0 := by
    apply Finset.sum_nonneg
    intro x _
    by_cases hx : 0 ≤ a x <;> simp [hx]
  rw [abs_of_nonneg hnonneg, sum_posPart_eq_half_sum_abs a hsum]

private def singletonMassDiff
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ω : Ω) : ℝ :=
  μ.real ({ω} : Set Ω) - ν.real ({ω} : Set Ω)

open Classical in
private lemma measureReal_sub_eq_sum_indicator_singletonMassDiff
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (S : Set Ω) :
    μ.real S - ν.real S =
      ∑ ω : Ω, if ω ∈ S then singletonMassDiff μ ν ω else 0 := by
  rw [FiniteMeasureSpace.measureReal_eq_sum_singletons μ S,
    FiniteMeasureSpace.measureReal_eq_sum_singletons ν S,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : ω ∈ S <;> simp [singletonMassDiff, hω]

private lemma sum_singletonMassDiff_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∑ ω : Ω, singletonMassDiff μ ν ω = 0 := by
  classical
  simp_rw [singletonMassDiff]
  rw [Finset.sum_sub_distrib]
  have hμ :=
    FiniteMeasureSpace.measureReal_eq_sum_singletons μ (Set.univ : Set Ω)
  have hν :=
    FiniteMeasureSpace.measureReal_eq_sum_singletons ν (Set.univ : Set Ω)
  simp only [Set.mem_univ, ↓reduceIte] at hμ hν
  rw [← hμ, ← hν]
  simp

open Classical in
/-- On a finite measurable space, total variation distance is half the `ℓ¹` distance between
the singleton masses. -/
theorem tvDistanceSup_eq_half_sum
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDistanceSup μ ν =
      (1 / 2 : ℝ) *
        ∑ ω : Ω, |μ.real ({ω} : Set Ω) -
          ν.real ({ω} : Set Ω)| := by
  let rhs : ℝ :=
    (1 / 2 : ℝ) *
      ∑ ω : Ω, |μ.real ({ω} : Set Ω) -
        ν.real ({ω} : Set Ω)|
  have hsum : ∑ ω : Ω, singletonMassDiff μ ν ω = 0 :=
    sum_singletonMassDiff_eq_zero μ ν
  have hset_le (S : {S : Set Ω // MeasurableSet S}) :
      |μ.real (S : Set Ω) - ν.real (S : Set Ω)| ≤ rhs := by
    rw [measureReal_sub_eq_sum_indicator_singletonMassDiff μ ν (S : Set Ω)]
    exact abs_sum_indicator_le_half_sum_abs (singletonMassDiff μ ν) hsum (S : Set Ω)
  have hrhs_nonneg : 0 ≤ rhs := by
    dsimp [rhs]
    positivity
  have hupper : tvDistanceSup μ ν ≤ rhs := by
    rw [tvDistanceSup]
    exact Real.sSup_le (by rintro _ ⟨S, rfl⟩; exact hset_le S) hrhs_nonneg
  let Spos : {S : Set Ω // MeasurableSet S} :=
    ⟨{ω | 0 ≤ singletonMassDiff μ ν ω}, MeasurableSet.of_discrete⟩
  have hpos_event :
      |μ.real (Spos : Set Ω) - ν.real (Spos : Set Ω)| = rhs := by
    rw [measureReal_sub_eq_sum_indicator_singletonMassDiff μ ν (Spos : Set Ω)]
    change |∑ ω : Ω, if 0 ≤ singletonMassDiff μ ν ω then singletonMassDiff μ ν ω else 0| =
      rhs
    rw [abs_sum_pos_indicator_eq_half_sum_abs (singletonMassDiff μ ν) hsum]
    rfl
  have hbdd :
      BddAbove (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |μ.real (S : Set Ω) - ν.real (S : Set Ω)|) := by
    exact ⟨rhs, by rintro _ ⟨S, rfl⟩; exact hset_le S⟩
  have hlower : rhs ≤ tvDistanceSup μ ν := by
    rw [tvDistanceSup]
    rw [← hpos_event]
    exact le_csSup hbdd (Set.mem_range_self Spos)
  exact le_antisymm hupper hlower

open Classical in
/-- On a finite measurable space, total variation distance is half the `ℓ¹` distance between
the singleton masses. -/
theorem tvDistance_eq_half_sum
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDistance μ ν =
      (1 / 2 : ℝ) *
        ∑ ω : Ω, |μ.real ({ω} : Set Ω) -
          ν.real ({ω} : Set Ω)| := by
  rw [tvDistance_eq_tvDistanceSup, tvDistanceSup_eq_half_sum]

/-- On `Bool`, total variation distance is the absolute singleton-mass gap at `true`. -/
theorem tvDistance_bool_eq_abs_true
    (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDistance μ ν =
      |μ.real ({true} : Set Bool) -
        ν.real ({true} : Set Bool)| := by
  rw [tvDistance_eq_half_sum]
  have hμ :
      μ.real ({false} : Set Bool) =
        1 - μ.real ({true} : Set Bool) := by
    have hcompl :
        ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by
      ext b
      cases b <;> simp
    rw [hcompl, measureReal_compl MeasurableSet.of_discrete, measureReal_univ_eq_one]
  have hν :
      ν.real ({false} : Set Bool) =
        1 - ν.real ({true} : Set Bool) := by
    have hcompl :
        ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by
      ext b
      cases b <;> simp
    rw [hcompl, measureReal_compl MeasurableSet.of_discrete, measureReal_univ_eq_one]
  rw [Fintype.sum_bool, hμ, hν]
  ring_nf
  rw [show (-μ.real ({true} : Set Bool) +
        ν.real ({true} : Set Bool)) =
      -(μ.real ({true} : Set Bool) -
        ν.real ({true} : Set Bool)) by ring]
  rw [abs_neg]
  ring

open Classical in
/-- The total variation distance between product distributions is bounded by the sum of the
total variation distances between their marginals. -/
theorem tvDistance_prod_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [FiniteMeasureSpace α] [FiniteMeasureSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    tvDistance (μ₁.prod μ₂) (ν₁.prod ν₂) ≤
      tvDistance μ₁ ν₁ + tvDistance μ₂ ν₂ := by
  let a : α → ℝ := fun x => μ₁.real ({x} : Set α)
  let b : β → ℝ := fun y => μ₂.real ({y} : Set β)
  let c : α → ℝ := fun x => ν₁.real ({x} : Set α)
  let d : β → ℝ := fun y => ν₂.real ({y} : Set β)
  have hb_sum : ∑ y : β, b y = 1 := by
    simp [b]
  have hc_sum : ∑ x : α, c x = 1 := by
    simp [c]
  have hb_nonneg : ∀ y, 0 ≤ b y := fun _ => measureReal_nonneg
  have hc_nonneg : ∀ x, 0 ≤ c x := fun _ => measureReal_nonneg
  rw [tvDistance_eq_half_sum, tvDistance_eq_half_sum, tvDistance_eq_half_sum]
  have hpoint (x : α) (y : β) :
      |a x * b y - c x * d y| ≤ |a x - c x| * b y + c x * |b y - d y| := by
    calc
      |a x * b y - c x * d y| =
          |(a x - c x) * b y + c x * (b y - d y)| := by
        ring_nf
      _ ≤ |(a x - c x) * b y| + |c x * (b y - d y)| := abs_add_le _ _
      _ = |a x - c x| * b y + c x * |b y - d y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hb_nonneg y), abs_of_nonneg (hc_nonneg x)]
  have hsum_le :
      ∑ p : α × β, |a p.1 * b p.2 - c p.1 * d p.2| ≤
        ∑ x : α, |a x - c x| + ∑ y : β, |b y - d y| := by
    calc
      ∑ p : α × β, |a p.1 * b p.2 - c p.1 * d p.2|
          = ∑ x : α, ∑ y : β, |a x * b y - c x * d y| := by
        rw [Fintype.sum_prod_type]
      _ ≤ ∑ x : α, ∑ y : β, (|a x - c x| * b y + c x * |b y - d y|) := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        exact hpoint x y
      _ = ∑ x : α, |a x - c x| + ∑ y : β, |b y - d y| := by
        calc
          ∑ x : α, ∑ y : β, (|a x - c x| * b y + c x * |b y - d y|)
              = ∑ x : α,
                  (|a x - c x| * ∑ y : β, b y +
                    c x * ∑ y : β, |b y - d y|) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_add_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
          _ = ∑ x : α, (|a x - c x| + c x * ∑ y : β, |b y - d y|) := by
            simp [hb_sum]
          _ = ∑ x : α, |a x - c x| + ∑ y : β, |b y - d y| := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, hc_sum, one_mul]
  convert (mul_le_mul_of_nonneg_left hsum_le (by norm_num : (0 : ℝ) ≤ 1 / 2)) using 1
  · apply congrArg ((1 / 2 : ℝ) * ·)
    apply Finset.sum_congr rfl
    intro p _
    rcases p with ⟨x, y⟩
    have hμ_prod :
        (μ₁.prod μ₂).real ({(x, y)} : Set (α × β)) = a x * b y := by
      change ((μ₁.prod μ₂) ({(x, y)} : Set (α × β))).toReal =
        a x * b y
      rw [show ({(x, y)} : Set (α × β)) = ({x} : Set α) ×ˢ ({y} : Set β) by
        ext p
        simp [Prod.ext_iff]]
      rw [Measure.prod_prod, ENNReal.toReal_mul]
      rfl
    have hν_prod :
        (ν₁.prod ν₂).real ({(x, y)} : Set (α × β)) = c x * d y := by
      change ((ν₁.prod ν₂) ({(x, y)} : Set (α × β))).toReal =
        c x * d y
      rw [show ({(x, y)} : Set (α × β)) = ({x} : Set α) ×ˢ ({y} : Set β) by
        ext p
        simp [Prod.ext_iff]]
      rw [Measure.prod_prod, ENNReal.toReal_mul]
      rfl
    simp [hμ_prod, hν_prod]
  · ring

end TVDistance

end CommunicationComplexity
