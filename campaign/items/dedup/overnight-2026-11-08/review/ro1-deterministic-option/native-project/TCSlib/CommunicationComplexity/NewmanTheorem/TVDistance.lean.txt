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

The total variation (statistical) distance between two probability measures, defined through
the total variation of the signed measure `μ − ν`, together with its two standard
characterisations: as the supremum over events of `|μ(S) − ν(S)|`, and, on a finite space,
as half the `ℓ¹` distance between the point masses. The file also records the two-point case
and subadditivity over products; the latter is used by the disjointness lower bound.

## Main definitions

- `signedMeasureDiff`: the signed measure `μ − ν` of two probability measures
- `tvDistance`: total variation distance, `½ ‖μ − ν‖` for the total variation norm of the
  signed measure `μ − ν`
- `tvDistanceSup`: total variation distance as the supremum over measurable events of
  `|μ(S) − ν(S)|`

## Main results

- `tvDistance_eq_tvDistanceSup`: the total-variation-mass definition agrees with the
  supremum-over-events definition
- `abs_measureReal_sub_le_tvDistance`: the total variation distance bounds the probability gap
  of every measurable event
- `tvDistance_nonneg`: total variation distance is nonnegative
- `tvDistanceSup_eq_half_sum`, `tvDistance_eq_half_sum`: on a finite measurable space, total
  variation distance is half the `ℓ¹` distance between the singleton masses
- `tvDistance_bool_eq_abs_true`: on `Bool`, total variation distance is the absolute
  singleton-mass gap at `true`
- `tvDistance_prod_le`: the total variation distance between product distributions is bounded
  by the sum of the total variation distances between their marginals

## References

* [LPW17] D. A. Levin, Y. Peres, with E. L. Wilmer, *Markov Chains and Mixing Times*,
  2nd ed., American Mathematical Society, 2017.
* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

open MeasureTheory

namespace CommunicationComplexity

/-- The signed difference between two probability measures, represented as measures with
`IsProbabilityMeasure` instances. -/
noncomputable def signedMeasureDiff {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : SignedMeasure Ω :=
  μ.toSignedMeasure - ν.toSignedMeasure

/-- Total variation distance between probability measures, defined as half the total mass of
the total variation `|μ − ν|` of the signed measure `μ - ν` (i.e. half of `P(Ω) + N(Ω)` for the
Jordan decomposition `μ − ν = P − N`). [LPW17, §4.1, eq. (4.1)] (statistical distance; also
the `|p − q|` of [RY20, Lemma 6.6]); deviation: LPW define it as the supremum over events
(`tvDistanceSup` here) and prove the other forms; `tvDistance_eq_tvDistanceSup` shows the two
agree. -/
noncomputable def tvDistance {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ

/-- Total variation distance between probability measures, defined as the supremum over
measurable events `S` of `|μ(S) − ν(S)|`. [LPW17, §4.1, eq. (4.1)] (statistical distance; also
the `|p − q|` of [RY20, Lemma 6.6]). -/
noncomputable def tvDistanceSup {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  sSup (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
    |μ.real (S : Set Ω) - ν.real (S : Set Ω)|)

namespace TVDistance

/-- A signed measure evaluated on a measurable set is the difference of the (real) masses of the
positive and negative parts of its Jordan decomposition. -/
private lemma signedMeasure_apply_eq_posPart_sub_negPart
    {Ω : Type*} [MeasurableSpace Ω] (s : SignedMeasure Ω)
    {S : Set Ω} (hS : MeasurableSet S) :
    s S =
      s.toJordanDecomposition.posPart.real S -
        s.toJordanDecomposition.negPart.real S := by
  conv_lhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition s]
  rw [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hS]

/-- The signed measure `μ − ν` of two probability measures gives the whole space mass `0`. -/
private lemma signedMeasureDiff_univ
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    signedMeasureDiff μ ν Set.univ = 0 := by
  rw [signedMeasureDiff, Measure.toSignedMeasure_sub_apply MeasurableSet.univ]
  simp

/-- For `μ − ν = P − N` (Jordan decomposition), the positive and negative parts have the same
total mass, `P(Ω) = N(Ω)`. -/
private lemma jordan_posPart_real_univ_eq_negPart_real_univ
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (signedMeasureDiff μ ν).toJordanDecomposition.posPart.real Set.univ =
      (signedMeasureDiff μ ν).toJordanDecomposition.negPart.real Set.univ := by
  have h := signedMeasure_apply_eq_posPart_sub_negPart (signedMeasureDiff μ ν) MeasurableSet.univ
  rw [signedMeasureDiff_univ μ ν] at h
  linarith

/-- The total mass of the total variation of a signed measure is `P(Ω) + N(Ω)` for its Jordan
decomposition. -/
private lemma totalVariation_real_univ
    {Ω : Type*} [MeasurableSpace Ω] (s : SignedMeasure Ω) :
    s.totalVariation.real Set.univ =
      s.toJordanDecomposition.posPart.real Set.univ +
        s.toJordanDecomposition.negPart.real Set.univ := by
  rw [SignedMeasure.totalVariation, measureReal_add_apply]

/-- Half the total variation mass of `μ − ν` equals the total mass `P(Ω)` of the positive part of
its Jordan decomposition. -/
private lemma half_totalVariation_real_univ_eq_posPart_real_univ
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ =
      (signedMeasureDiff μ ν).toJordanDecomposition.posPart.real Set.univ := by
  rw [totalVariation_real_univ]
  rw [jordan_posPart_real_univ_eq_negPart_real_univ μ ν]
  ring

/-- For every measurable event `S`, `|(μ − ν)(S)|` is at most half the total variation mass of
`μ − ν`: writing `μ − ν = P − N`, both `P(S)` and `N(S)` lie in `[0, P(Ω)]`.

**Proof sketch.** Let `P`, `N` be the Jordan parts of `μ − ν`. (1) `P(Ω) = N(Ω)`, because `μ`
and `ν` are both probability measures. (2) By monotonicity and nonnegativity, `P(S)` and `N(S)`
both lie in `[0, P(Ω)]`, so `|P(S) − N(S)| ≤ P(Ω)`. (3) Rewrite half the total variation mass
as `P(Ω)` and `(μ − ν)(S)` as `P(S) − N(S)`. -/
private lemma event_abs_signedMeasureDiff_le_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : {S : Set Ω // MeasurableSet S}) :
    |signedMeasureDiff μ ν (S : Set Ω)| ≤
      (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  let P := (signedMeasureDiff μ ν).toJordanDecomposition.posPart
  let N := (signedMeasureDiff μ ν).toJordanDecomposition.negPart
  -- Step 1: `P(Ω) = N(Ω)`
  have hPN : P.real Set.univ = N.real Set.univ := by
    simpa [P, N] using jordan_posPart_real_univ_eq_negPart_real_univ μ ν
  -- Step 2: `P(S)`, `N(S)` lie in `[0, P(Ω)]`, so `|P(S) − N(S)| ≤ P(Ω)`
  have hPmono : P.real (S : Set Ω) ≤ P.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hNmono : N.real (S : Set Ω) ≤ N.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hPnonneg : 0 ≤ P.real (S : Set Ω) := measureReal_nonneg
  have hNnonneg : 0 ≤ N.real (S : Set Ω) := measureReal_nonneg
  have hbound :
      |P.real (S : Set Ω) - N.real (S : Set Ω)| ≤ P.real Set.univ := by
    rw [abs_le]
    constructor <;> linarith
  -- Step 3: rewrite both sides in terms of `P` and `N`
  rw [half_totalVariation_real_univ_eq_posPart_real_univ μ ν]
  rw [signedMeasure_apply_eq_posPart_sub_negPart (signedMeasureDiff μ ν) S.property]
  simpa [P, N] using hbound

/-- For every measurable event `S`, `|μ(S) − ν(S)|` is at most half the total variation mass of
`μ − ν`. -/
private lemma event_abs_measureReal_sub_le_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : {S : Set Ω // MeasurableSet S}) :
    |μ.real (S : Set Ω) - ν.real (S : Set Ω)| ≤
      (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  rw [← Measure.toSignedMeasure_sub_apply S.property]
  simpa [signedMeasureDiff] using event_abs_signedMeasureDiff_le_half_totalVariation μ ν S

/-- Some measurable event attains half the total variation mass of `μ − ν`: the complement of a
Hahn-decomposition negative set, on which `N` vanishes and `P` has full mass.

**Proof sketch.** Take a measurable set `S` from the Hahn decomposition of `μ − ν` such that
the positive part `P` vanishes on `S` and the negative part `N` vanishes on `Sᶜ`; the event is
`Sᶜ`. (1) Since `P(S) = 0`, `P(Sᶜ) = P(Ω)`. (2) `N(Sᶜ) = 0`. (3) Hence
`(μ − ν)(Sᶜ) = P(Sᶜ) − N(Sᶜ) = P(Ω) ≥ 0`, which is half the total variation mass. -/
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
  -- Step 1: `P(S) = 0`, so `P(Sᶜ) = P(Ω)`
  have hPzero_real : P.real S = 0 := by
    rw [measureReal_def, show P S = 0 by simpa [P] using hPzero, ENNReal.toReal_zero]
  have hPcompl : P.real Sᶜ = P.real Set.univ := by
    rw [measureReal_compl hS, hPzero_real]
    ring
  -- Step 2: `N(Sᶜ) = 0`
  have hNcompl : N.real Sᶜ = 0 := by
    rw [measureReal_def, hNzero, ENNReal.toReal_zero]
  have hnonneg : 0 ≤ P.real Set.univ := measureReal_nonneg
  -- Step 3: `(μ − ν)(Sᶜ) = P(Ω)`, the half total variation
  rw [signedMeasure_apply_eq_posPart_sub_negPart s hS.compl]
  rw [half_totalVariation_real_univ_eq_posPart_real_univ μ ν]
  simp [s, P, N, hPcompl, hNcompl, abs_of_nonneg hnonneg]

/-- Some measurable event `S` satisfies `|μ(S) − ν(S)| = ½ ‖μ − ν‖`. -/
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
/-- The total-variation-mass definition agrees with the supremum-over-events definition:
`½ ‖μ − ν‖ = sup_S |μ(S) − ν(S)|` over measurable events `S`. [LPW17, §4.1, eq. (4.1) and
Prop. 4.2] (LPW take the supremum as the definition and prove, in the finite case, that it is
half the `ℓ¹` norm; here the identification goes through the Jordan/Hahn decomposition and
holds on any measurable space).

**Proof sketch.** Write `μ − ν = P − N` for the Jordan decomposition; then `P(Ω) = N(Ω)`, so half
the total variation mass is `P(Ω)`.
Step 1 (upper bound): for every event `S`, `|μ(S) − ν(S)| = |P(S) − N(S)| ≤ P(Ω)`, hence the
supremum is at most `P(Ω)`.
Step 2 (attained): the complement of a Hahn negative set carries all of `P` and none of `N`, so
its gap is exactly `P(Ω)`; hence `P(Ω)` is at most the supremum. Conclude by antisymmetry. -/
theorem tvDistance_eq_tvDistanceSup
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDistance μ ν = tvDistanceSup μ ν := by
  let rhs : ℝ := (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ
  -- Step 1: every event gap is at most half the total variation mass
  have hset_le (S : {S : Set Ω // MeasurableSet S}) :
      |μ.real (S : Set Ω) - ν.real (S : Set Ω)| ≤ rhs := by
    simpa [rhs] using event_abs_measureReal_sub_le_half_totalVariation μ ν S
  have hrhs_nonneg : 0 ≤ rhs := by
    dsimp [rhs]
    positivity
  have hupper : tvDistanceSup μ ν ≤ rhs := by
    rw [tvDistanceSup]
    exact Real.sSup_le (by rintro _ ⟨S, rfl⟩; exact hset_le S) hrhs_nonneg
  -- Step 2: the Hahn-decomposition event attains it
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

/-- The total variation distance bounds the probability gap of every measurable event:
`|μ(S) − ν(S)| ≤ TV(μ, ν)` for all measurable `S`. -/
theorem abs_measureReal_sub_le_tvDistance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : {S : Set Ω // MeasurableSet S}) :
    |μ.real (S : Set Ω) - ν.real (S : Set Ω)| ≤
      tvDistance μ ν := by
  rw [tvDistance]
  exact event_abs_measureReal_sub_le_half_totalVariation μ ν S

/-- Total variation distance is nonnegative: `0 ≤ TV(μ, ν)`. -/
theorem tvDistance_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ tvDistance μ ν := by
  rw [tvDistance]
  positivity

open Classical in
/-- The sum of a real-valued function over any subset is at most the sum of its positive part
over the whole finite type. -/
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
/-- If a real-valued function on a finite type sums to `0`, the sum of its positive part is half
the sum of its absolute value.

**Proof sketch.** Pointwise `|a x| = 2·max(a x, 0) − a x`, by cases on the sign of `a x`.
Summing, `Σ |a| = 2·Σ max(a, 0) − Σ a = 2·Σ max(a, 0)` because `Σ a = 0`; divide by `2`. -/
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
/-- If a real-valued function `a` on a finite type sums to `0`, then for every subset `S`,
`|Σ_{x ∈ S} a x| ≤ ½ Σ_x |a x|`.

**Proof sketch.** The positive-part sum `pos` equals `½ Σ |a|`. The sums over `S` and over `Sᶜ`
are both at most `pos`, and they add up to `Σ a = 0`, so the sum over `S` lies in
`[−pos, pos]`. -/
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
/-- If a real-valued function on a finite type sums to `0`, the absolute value of the sum of its
positive part is exactly half the sum of its absolute value (the bound of
`abs_sum_indicator_le_half_sum_abs` is attained by the set where the function is nonnegative). -/
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

/-- The pointwise mass difference `μ {ω} − ν {ω}` of two probability measures. -/
private def singletonMassDiff
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ω : Ω) : ℝ :=
  μ.real ({ω} : Set Ω) - ν.real ({ω} : Set Ω)

open Classical in
/-- On a finite measurable space, `μ(S) − ν(S)` is the sum over `ω ∈ S` of the singleton mass
differences `μ {ω} − ν {ω}`. -/
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

/-- On a finite measurable space, the singleton mass differences of two probability measures
sum to `0`. -/
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
/-- On a finite measurable space, the supremum-over-events total variation distance is half the
`ℓ¹` distance between the singleton masses: `sup_S |μ(S) − ν(S)| = ½ Σ_ω |μ {ω} − ν {ω}|`.
[LPW17, Prop. 4.2] (`‖μ − ν‖_TV = ½ Σ_x |μ(x) − ν(x)|`).

**Proof sketch.** Let `a ω = μ {ω} − ν {ω}`; these differences sum to `0`.
Step 1 (upper bound): for every event `S`, `μ(S) − ν(S) = Σ_{ω ∈ S} a ω`, and for a mean-zero
family such a partial sum is bounded in absolute value by `½ Σ |a|`
(`abs_sum_indicator_le_half_sum_abs`); hence the supremum is at most `½ Σ |a|`.
Step 2 (attained): the event `{a ≥ 0}` has gap exactly `½ Σ |a|`
(`abs_sum_pos_indicator_eq_half_sum_abs`), so `½ Σ |a|` is at most the supremum. Conclude by
antisymmetry. -/
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
  -- Step 1: every event gap is a partial sum of the mean-zero differences, hence `≤ rhs`
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
  -- Step 2: the event where `μ` dominates `ν` attains `rhs`
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
the singleton masses: `TV(μ, ν) = ½ Σ_ω |μ {ω} − ν {ω}|`. [LPW17, Prop. 4.2]
(`‖μ − ν‖_TV = ½ Σ_x |μ(x) − ν(x)|`). -/
theorem tvDistance_eq_half_sum
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDistance μ ν =
      (1 / 2 : ℝ) *
        ∑ ω : Ω, |μ.real ({ω} : Set Ω) -
          ν.real ({ω} : Set Ω)| := by
  rw [tvDistance_eq_tvDistanceSup, tvDistanceSup_eq_half_sum]

/-- On `Bool`, the mass at `false` is one minus the mass at `true`. -/
private lemma measureReal_false_eq_one_sub_true
    (μ : Measure Bool) [IsProbabilityMeasure μ] :
    μ.real ({false} : Set Bool) = 1 - μ.real ({true} : Set Bool) := by
  have hcompl : ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by
    ext b
    cases b <;> simp
  rw [hcompl, measureReal_compl MeasurableSet.of_discrete, measureReal_univ_eq_one]

/-- On `Bool`, total variation distance is the absolute singleton-mass gap at `true`:
`TV(μ, ν) = |μ {true} − ν {true}|`. [LPW17, Prop. 4.2] (two-point case of the half-`ℓ¹`
formula: the two summands coincide). -/
theorem tvDistance_bool_eq_abs_true
    (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDistance μ ν =
      |μ.real ({true} : Set Bool) -
        ν.real ({true} : Set Bool)| := by
  -- Step 1: TV is the half-sum over `Bool`; express both `false` masses via the `true` masses
  rw [tvDistance_eq_half_sum, Fintype.sum_bool,
    measureReal_false_eq_one_sub_true μ, measureReal_false_eq_one_sub_true ν]
  -- Step 2: the `false` summand equals the `true` summand
  rw [show (1 - μ.real ({true} : Set Bool)) - (1 - ν.real ({true} : Set Bool)) =
      -(μ.real ({true} : Set Bool) - ν.real ({true} : Set Bool)) by ring, abs_neg]
  ring

/-- Pointwise triangle bound for a product gap: `|ab - cd| ≤ |a - c| b + c |b - d|` when
`b, c ≥ 0`. -/
private lemma abs_mul_sub_mul_le {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |a * b - c * d| ≤ |a - c| * b + c * |b - d| := by
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by ring_nf
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * b + c * |b - d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hc]

/-- The `ℓ¹` gap between two product weight functions is at most the sum of the marginal
`ℓ¹` gaps, given that `b` and `c` are nonnegative and sum to `1`.

**Proof sketch.** Write the sum over pairs as a double sum and bound each term by the
pointwise triangle inequality `|ab − cd| ≤ |a − c|·b + c·|b − d|` (`abs_mul_sub_mul_le`,
valid since `b, c ≥ 0`). Summing over `y` first, the first term contributes
`|a x − c x| · Σ b = |a x − c x|` and the second `c x · Σ |b − d|`; summing over `x` and using
`Σ c = 1` gives the bound. -/
private lemma sum_prod_abs_le {α β : Type*} [Fintype α] [Fintype β]
    (a c : α → ℝ) (b d : β → ℝ)
    (hb_nonneg : ∀ y, 0 ≤ b y) (hc_nonneg : ∀ x, 0 ≤ c x)
    (hb_sum : ∑ y : β, b y = 1) (hc_sum : ∑ x : α, c x = 1) :
    ∑ p : α × β, |a p.1 * b p.2 - c p.1 * d p.2| ≤
      ∑ x : α, |a x - c x| + ∑ y : β, |b y - d y| := by
  calc
    ∑ p : α × β, |a p.1 * b p.2 - c p.1 * d p.2|
        = ∑ x : α, ∑ y : β, |a x * b y - c x * d y| := by
      rw [Fintype.sum_prod_type]
    _ ≤ ∑ x : α, ∑ y : β, (|a x - c x| * b y + c x * |b y - d y|) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        abs_mul_sub_mul_le (hb_nonneg y) (hc_nonneg x)
    _ = ∑ x : α, (|a x - c x| * ∑ y : β, b y + c x * ∑ y : β, |b y - d y|) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = ∑ x : α, (|a x - c x| + c x * ∑ y : β, |b y - d y|) := by
      simp [hb_sum]
    _ = ∑ x : α, |a x - c x| + ∑ y : β, |b y - d y| := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hc_sum, one_mul]

/-- The singleton mass of a product measure is the product of the singleton masses. -/
private lemma prod_measureReal_singleton
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ : Measure α) (μ₂ : Measure β) [SigmaFinite μ₂] (x : α) (y : β) :
    (μ₁.prod μ₂).real ({(x, y)} : Set (α × β)) = μ₁.real ({x} : Set α) * μ₂.real ({y} : Set β) := by
  change ((μ₁.prod μ₂) ({(x, y)} : Set (α × β))).toReal = _
  rw [show ({(x, y)} : Set (α × β)) = ({x} : Set α) ×ˢ ({y} : Set β) by
    ext p
    simp [Prod.ext_iff]]
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  rfl

open Classical in
/-- The total variation distance between product distributions on finite spaces is bounded by
the sum of the total variation distances between their marginals:
`TV(μ₁ ⊗ μ₂, ν₁ ⊗ ν₂) ≤ TV(μ₁, ν₁) + TV(μ₂, ν₂)`. [LPW17, Exercise 4.4] (the two-factor
case `n = 2` of subadditivity of total variation over products; standard via the coupling
characterisation [LPW17, Prop. 4.7], but
proved here directly from the half-`ℓ¹` formula, which is why finiteness of both factors is
assumed).

**Proof sketch.** Let `a, c` be the point masses of `μ₁, ν₁` and `b, d` those of `μ₂, ν₂`.
Step 1: rewrite all three distances as half-sums of absolute point-mass differences
(`tvDistance_eq_half_sum`).
Step 2: the weights `b` and `c` are nonnegative and sum to `1`.
Step 3: the pointwise triangle bound `|a b − c d| ≤ |a − c| b + c |b − d|` summed over
pairs, using Step 2 to collapse `Σ b = Σ c = 1`, gives
`Σ_{(x,y)} |a x b y − c x d y| ≤ Σ_x |a x − c x| + Σ_y |b y − d y|` (`sum_prod_abs_le`).
Step 4: the point masses of a product measure are the products of the marginal point masses,
so the left side of Step 3 is the product `ℓ¹` gap; halve and conclude. -/
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
  -- Step 1: rewrite all three total variation distances as half-sums
  rw [tvDistance_eq_half_sum, tvDistance_eq_half_sum, tvDistance_eq_half_sum]
  -- Step 2: the marginal weights `b`, `c` are nonnegative and sum to `1`
  have hb_sum : ∑ y : β, b y = 1 := by simp [b]
  have hc_sum : ∑ x : α, c x = 1 := by simp [c]
  have hb_nonneg : ∀ y, 0 ≤ b y := fun _ => measureReal_nonneg
  have hc_nonneg : ∀ x, 0 ≤ c x := fun _ => measureReal_nonneg
  -- Step 3: the `ℓ¹` gap of the product weights is bounded by the sum of the marginal gaps
  have hsum_le :
      ∑ p : α × β, |a p.1 * b p.2 - c p.1 * d p.2| ≤
        ∑ x : α, |a x - c x| + ∑ y : β, |b y - d y| :=
    sum_prod_abs_le a c b d hb_nonneg hc_nonneg hb_sum hc_sum
  -- Step 4: identify the product singleton masses with the products of the marginal masses
  have hμ_prod (x : α) (y : β) :
      (μ₁.prod μ₂).real ({(x, y)} : Set (α × β)) = a x * b y :=
    prod_measureReal_singleton μ₁ μ₂ x y
  have hν_prod (x : α) (y : β) :
      (ν₁.prod ν₂).real ({(x, y)} : Set (α × β)) = c x * d y :=
    prod_measureReal_singleton ν₁ ν₂ x y
  convert (mul_le_mul_of_nonneg_left hsum_le (by norm_num : (0 : ℝ) ≤ 1 / 2)) using 1
  · apply congrArg ((1 / 2 : ℝ) * ·)
    apply Finset.sum_congr rfl
    intro p _
    obtain ⟨x, y⟩ := p
    simp [hμ_prod, hν_prod]
  · ring

end TVDistance

end CommunicationComplexity
