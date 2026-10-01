/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.DualHardSample
import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Disjointness lower bound: masses under the hard distribution

Probabilities of the basic events of Razborov's hard distribution for set disjointness
[RY20, Ch. 6, 'Hard distribution'], and the two conditioned laws used in the proof of
[RY20, Thm 6.13]: the hard distribution conditioned on the disjoint event `𝒟`
(`disjointCondMeasure`, the law `p(ab | 𝒟)` of [RY20, Ch. 6, eq. (6.3)]) and its further
conditioning on Bob's special bit being `0` (`disjointSpecialYFalseMeasure`). Every mass is
computed from the four-field product formula `hardSample_measureReal_fieldProduct`: the
special coordinate `T`, the two special bits and the remaining coordinate vector are
independent and uniform. The file ends with the two facts about the uniform
disjoint-coordinate-vector law that later files feed into the chain rule of
[RY20, Lemma 6.15]: it is a product measure, so its coordinates are mutually independent.

## Main definitions

* `disjointCondMeasure`: the hard distribution conditioned on the disjoint event `𝒟`.
* `disjointSpecialYFalseMeasure`: `disjointCondMeasure` further conditioned on `Y_T = 0`.

## Main results

* `hardSample_measureReal_fieldProduct`: the mass of an event that constrains the four
  fields separately is the product of the four factor masses.
* `measureReal_specialIntersect`, `measureReal_disjointEvent`,
  `measureReal_specialCoordinateEvent`, `measureReal_specialBitsEvent`, and the
  intersection variants: `Pr[A ∩ B ≠ ∅] = 1/4`, `Pr[𝒟] = 3/4`, `Pr[T = i] = 1/n`,
  `Pr[(X_T, Y_T) = (b, b')] = 1/4`.
* `disjointCondMeasure_measureReal_specialCoordinateEvent`,
  `disjointCondMeasure_measureReal_specialBitsEvent`,
  `disjointCondMeasure_measureReal_specialY_false`: under `𝒟`, `T` is still uniform, each
  non-intersecting special bit pair has mass `1/3`, and `p(b_T = 0 | 𝒟) = 2/3`.
* `disjointSpecialYFalseMeasure_measureReal_specialX_singleton`: under `𝒟 ∧ Y_T = 0`,
  Alice's special bit is uniform.
* `disjointCondMeasure_measureReal_disjointModel_fiber`,
  `disjointCondMeasure_measureReal_specialCoordinate_disjointCoordinateVector_fiber`: under
  `𝒟` the disjoint model `(T, coords, junk)` is uniform, hence so is `(T, coords)`.
* `uniformDisjointCoordinateVector_eq_pi`, `uniformDisjointCoordinateVector_iIndepFun`: the
  uniform disjoint-vector law is the product of the one-coordinate uniform laws, so its
  coordinates are mutually independent.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Raz92] A. A. Razborov, "On the distributional complexity of disjointness",
  *Theoretical Computer Science* 106(2):385–390, 1992.
* [KS92] B. Kalyanasundaram, G. Schnitger, "The probabilistic communication complexity of
  set intersection", *SIAM J. Discrete Math.* 5(4):545–557, 1992.
* [BJKS04] Z. Bar-Yossef, T. S. Jayram, R. Kumar, D. Sivakumar, "An information statistics
  approach to data stream and communication complexity", *J. Comput. Syst. Sci.*
  68(4):702–732, 2004.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Functions.Disjointness

namespace RandomizedLowerBound

variable (n : ℕ+)

open Classical in
/-- Under the hard distribution, the probability that the special coordinate lies in `TSet`,
Alice's special bit in `XSet`, Bob's special bit in `YSet` and the remaining coordinate
vector in `OtherSet` is the product of the four masses `Pr[T ∈ TSet] · Pr[X_T ∈ XSet] ·
Pr[Y_T ∈ YSet] · Pr[other ∈ OtherSet]` under the respective uniform laws; that is, the hard
sample distribution is the product distribution on the independent fields `T`, `X_T`, `Y_T`
and `other` [RY20, Ch. 6, 'Hard distribution'] (the index `T`, the two bits at `T` and the
off-`T` pairs are sampled independently). This rectangle form is the most convenient way to
compute probabilities of events depending separately on the four fields.

**Proof sketch.** The ambient measure is uniform on the finite type `HardSample n`, so the
mass of the event is its cardinality divided by `|HardSample n| = n · 4 · 3 ^ n`.
Step 1: rewrite the mass as a ratio of cardinalities (`uniformOn_univ_measureReal_eq_card_subtype`).
Step 2: the samples in the event are in explicit bijection with the product of the four
subtypes `{T ∈ TSet} × {x ∈ XSet} × {y ∈ YSet} × {other ∈ OtherSet}`, so the numerator is
the product of the four cardinalities (`Fintype.card_congr`). Step 3: each factor law is
uniform, so its mass of a set is that set's cardinality over `n`, `2`, `2`, `3 ^ n`
respectively; with `HardSample.card` for the denominator, clearing denominators identifies
the two sides. -/
theorem hardSample_measureReal_fieldProduct
    (TSet : Set (Fin n)) (XSet YSet : Set Bool)
    (OtherSet : Set (Fin n → DisjointCoordinate)) :
    volume.real
        {ω : HardSample n |
          ω.T ∈ TSet ∧ ω.xT ∈ XSet ∧ ω.yT ∈ YSet ∧ ω.other ∈ OtherSet} =
      (uniformFin n).real TSet *
        uniformBool.real XSet *
          uniformBool.real YSet *
            (uniformDisjointCoordinateVector n).real OtherSet := by
  let sampleEvent : Set (HardSample n) :=
    {ω | ω.T ∈ TSet ∧ ω.xT ∈ XSet ∧ ω.yT ∈ YSet ∧ ω.other ∈ OtherSet}
  -- Step 1: the uniform mass of the event is `|event| / |HardSample n|`.
  change volume.real sampleEvent = _
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real sampleEvent) = _
  rw [Measure.real, uniformOn_univ_measureReal_eq_card_subtype]
  -- Step 2: the event is in bijection with the product of the four factor subtypes.
  rw [show
      Fintype.card {ω : HardSample n // ω ∈ sampleEvent} =
        Fintype.card {T : Fin n // T ∈ TSet} *
          Fintype.card {x : Bool // x ∈ XSet} *
            Fintype.card {y : Bool // y ∈ YSet} *
              Fintype.card {other : Fin n → DisjointCoordinate // other ∈ OtherSet} by
    let e :
        {ω : HardSample n // ω ∈ sampleEvent} ≃
          {T : Fin n // T ∈ TSet} × {x : Bool // x ∈ XSet} ×
            {y : Bool // y ∈ YSet} ×
              {other : Fin n → DisjointCoordinate // other ∈ OtherSet} := {
      toFun := fun ω =>
        (⟨ω.1.T, ω.2.1⟩, ⟨ω.1.xT, ω.2.2.1⟩,
          ⟨ω.1.yT, ω.2.2.2.1⟩, ⟨ω.1.other, ω.2.2.2.2⟩)
      invFun := fun z =>
        ⟨{ T := z.1.1
           xT := z.2.1.1
           yT := z.2.2.1.1
           other := z.2.2.2.1 },
          ⟨z.1.2, z.2.1.2, z.2.2.1.2, z.2.2.2.2⟩⟩
      left_inv := by
        intro ω
        rcases ω with ⟨⟨T, xT, yT, other⟩, hω⟩
        rfl
      right_inv := by
        intro z
        rcases z with ⟨⟨T, hT⟩, ⟨xT, hxT⟩, ⟨yT, hyT⟩, ⟨other, hother⟩⟩
        rfl }
    simpa [Fintype.card_prod, Nat.mul_assoc] using Fintype.card_congr e]
  -- Step 3: each factor mass is a ratio of cardinalities; clear denominators.
  rw [uniformFin_real n TSet, uniformBool_real XSet, uniformBool_real YSet,
    uniformDisjointCoordinateVector_real n OtherSet]
  rw [HardSample.card]
  have hn : (n : ℝ) ≠ 0 := by positivity
  have hpow : (3 ^ (n : ℕ) : ℝ) ≠ 0 := by positivity
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp [hn, hpow]
  ring

open Classical in
/-- Under the hard distribution, the event that both special bits are `true` (so that the
generated sets intersect, necessarily exactly at `T`) has probability `1 / 4`
[RY20, Ch. 6, 'they intersect with probability 1/4']. -/
theorem measureReal_specialIntersect :
    volume.real (specialIntersect n) = (1 / 4 : ℝ) := by
  rw [show specialIntersect n =
      {ω : HardSample n |
        ω.T ∈ Set.univ ∧ ω.xT ∈ ({true} : Set Bool) ∧
          ω.yT ∈ ({true} : Set Bool) ∧
            ω.other ∈ (Set.univ : Set (Fin n → DisjointCoordinate))} by
    ext ω
    simp [specialIntersect]]
  rw [hardSample_measureReal_fieldProduct]
  rw [uniformFin_univ, uniformDisjointCoordinateVector_univ, uniformBool_singleton true]
  norm_num

open Classical in
/-- Under the hard distribution, each prescribed value `(bx, bY)` of the pair of special
bits `(X_T, Y_T)` has probability `1 / 4`. -/
theorem measureReal_specialBitsEvent (bx bY : Bool) :
    volume.real (specialBitsEvent n bx bY) = (1 / 4 : ℝ) := by
  rw [show specialBitsEvent n bx bY =
      {ω : HardSample n |
        ω.T ∈ Set.univ ∧ ω.xT ∈ ({bx} : Set Bool) ∧
          ω.yT ∈ ({bY} : Set Bool) ∧
            ω.other ∈ (Set.univ : Set (Fin n → DisjointCoordinate))} by
    ext ω
    simp [specialBitsEvent]]
  rw [hardSample_measureReal_fieldProduct]
  rw [uniformFin_univ, uniformDisjointCoordinateVector_univ,
    uniformBool_singleton bx, uniformBool_singleton bY]
  norm_num

open Classical in
/-- Under the hard distribution, the special coordinate `T` takes each value `i` with
probability `1 / n`. -/
theorem measureReal_specialCoordinateEvent (i : Fin n) :
    volume.real (specialCoordinateEvent n i) = (1 / (n : ℝ) : ℝ) := by
  rw [show specialCoordinateEvent n i =
      {ω : HardSample n |
        ω.T ∈ ({i} : Set (Fin n)) ∧ ω.xT ∈ Set.univ ∧
          ω.yT ∈ Set.univ ∧
            ω.other ∈ (Set.univ : Set (Fin n → DisjointCoordinate))} by
    ext ω
    simp [specialCoordinateEvent]]
  rw [hardSample_measureReal_fieldProduct]
  rw [uniformFin_singleton, uniformBool_univ, uniformDisjointCoordinateVector_univ]
  ring

open Classical in
/-- Under the hard distribution, the event that `T = i` and both special bits are `true`
has probability `1 / (4n)`. -/
theorem measureReal_specialCoordinateEvent_inter_specialIntersect (i : Fin n) :
    volume.real (specialCoordinateEvent n i ∩ specialIntersect n) =
      (1 / (4 * (n : ℝ)) : ℝ) := by
  rw [show specialCoordinateEvent n i ∩ specialIntersect n =
      {ω : HardSample n |
        ω.T ∈ ({i} : Set (Fin n)) ∧ ω.xT ∈ ({true} : Set Bool) ∧
          ω.yT ∈ ({true} : Set Bool) ∧
            ω.other ∈ (Set.univ : Set (Fin n → DisjointCoordinate))} by
    ext ω
    simp [specialCoordinateEvent, specialIntersect]]
  rw [hardSample_measureReal_fieldProduct]
  rw [uniformFin_singleton, uniformDisjointCoordinateVector_univ, uniformBool_singleton true]
  ring

/-- Under the hard distribution, the event `(X_T, Y_T) = (0, 0)` has probability `1 / 4`. -/
theorem measureReal_specialZeroZero :
    volume.real (specialZeroZero n) = (1 / 4 : ℝ) := by
  rw [specialZeroZero, measureReal_specialBitsEvent]

/-- Under the hard distribution, the event `Y_T = 0` has probability `1 / 2`. -/
theorem measureReal_specialY_false :
    volume.real (((specialY n) ⁻¹' {false}) : Set (HardSample n)) = (1 / 2 : ℝ) := by
  rw [show ((specialY n) ⁻¹' {false} : Set (HardSample n)) =
      {ω : HardSample n |
        ω.T ∈ Set.univ ∧ ω.xT ∈ Set.univ ∧
          ω.yT ∈ ({false} : Set Bool) ∧
            ω.other ∈ (Set.univ : Set (Fin n → DisjointCoordinate))} by
    ext ω
    simp [specialY]]
  rw [hardSample_measureReal_fieldProduct]
  rw [uniformFin_univ, uniformBool_univ, uniformDisjointCoordinateVector_univ,
    uniformBool_singleton false]
  norm_num

/-- The disjoint event `𝒟` is the complement of the event that both special bits are
`true`: the generated sets are disjoint exactly when they do not both contain `T`. -/
theorem disjointEvent_eq_compl_specialIntersect :
    disjointEvent n = (specialIntersect n)ᶜ := by
  ext ω
  simp [disjointEvent, specialIntersect, disjoint_X_Y_iff]

/-- Under the hard distribution, the generated inputs are disjoint with probability
`3 / 4`; that is, `Pr[𝒟] = 3/4` [RY20, Ch. 6, 'they intersect with probability 1/4']
(stated there as the complementary `1/4`). -/
theorem measureReal_disjointEvent :
    volume.real (disjointEvent n) = (3 / 4 : ℝ) := by
  rw [disjointEvent_eq_compl_specialIntersect]
  rw [measureReal_compl MeasurableSet.of_discrete]
  rw [measureReal_univ_eq_one]
  rw [show volume.real (specialIntersect n) = (1 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_specialIntersect n]
  norm_num

open Classical in
/-- Under the hard distribution, the event that `T = i` and the generated inputs are
disjoint has probability `3 / (4n)`.

**Proof sketch.** Step 1: since `𝒟` is the complement of the special-intersection event,
`{T = i} ∩ 𝒟` is `{T = i}` with `{T = i} ∩ {X_T = Y_T = 1}` removed. Step 2: the mass of a
set difference is the difference of the masses (`measureReal_diff`), which are `1 / n` and
`1 / (4n)` by the product formula, so the result is `3 / (4n)`. -/
theorem measureReal_specialCoordinateEvent_inter_disjointEvent (i : Fin n) :
    volume.real (specialCoordinateEvent n i ∩ disjointEvent n) =
      (3 / (4 * (n : ℝ)) : ℝ) := by
  -- Step 1: write `{T = i} ∩ 𝒟` as a set difference.
  have hset :
      specialCoordinateEvent n i ∩ disjointEvent n =
        specialCoordinateEvent n i \ (specialCoordinateEvent n i ∩ specialIntersect n) := by
    rw [disjointEvent_eq_compl_specialIntersect]
    ext ω
    simp
  change volume.real (specialCoordinateEvent n i ∩ disjointEvent n) =
    (3 / (4 * (n : ℝ)) : ℝ)
  rw [hset]
  -- Step 2: subtract the masses `1 / n` and `1 / (4n)`.
  rw [measureReal_diff]
  · rw [show volume.real (specialCoordinateEvent n i) =
        (1 / (n : ℝ) : ℝ) by
      simpa [Measure.real] using measureReal_specialCoordinateEvent n i]
    rw [show volume.real
        (specialCoordinateEvent n i ∩ specialIntersect n) =
          (1 / (4 * (n : ℝ)) : ℝ) by
      simpa [Measure.real] using measureReal_specialCoordinateEvent_inter_specialIntersect n i]
    have hn : (n : ℝ) ≠ 0 := by positivity
    field_simp [hn]
    ring
  · exact Set.inter_subset_left
  · exact MeasurableSet.of_discrete

/-- The disjoint event `𝒟` has nonzero measure under the hard distribution (its mass is
`3 / 4`), so conditioning on it is meaningful. -/
theorem measure_disjointEvent_ne_zero :
    volume (disjointEvent n) ≠ 0 := by
  have hreal :
      volume.real (disjointEvent n) ≠ 0 := by
    rw [measureReal_disjointEvent n]
    norm_num
  exact (ENNReal.toReal_ne_zero.mp hreal).1

/-- The hard distribution conditioned on the generated input being disjoint: the law
`p(ab | 𝒟)` to which the chain-rule lemma is applied [RY20, Ch. 6, eq. (6.3)]. -/
noncomputable def disjointCondMeasure : Measure (HardSample n) :=
  volume[|disjointEvent n]

open Classical in
/-- Under the disjoint-conditioned hard distribution, the special coordinate `T` remains
uniform: each value `i` has mass `1 / n`. -/
theorem disjointCondMeasure_measureReal_specialCoordinateEvent (i : Fin n) :
    (disjointCondMeasure n).real (specialCoordinateEvent n i) =
      (1 / (n : ℝ) : ℝ) := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hinter :
      disjointEvent n ∩ specialCoordinateEvent n i =
        specialCoordinateEvent n i ∩ disjointEvent n := by
    rw [Set.inter_comm]
  have hnum :
      volume.real (specialCoordinateEvent n i ∩ disjointEvent n) =
        (3 / (4 * (n : ℝ)) : ℝ) := by
    simpa [Measure.real] using measureReal_specialCoordinateEvent_inter_disjointEvent n i
  have hden : volume.real (disjointEvent n) = (3 / 4 : ℝ) := by
    simpa [Measure.real] using measureReal_disjointEvent n
  rw [hinter, hnum, hden]
  have hn : (n : ℝ) ≠ 0 := by positivity
  field_simp [hn]

/-- The preimage of `{i}` under the special-coordinate variable `T` is the event
`specialCoordinateEvent n i` that `T = i`. -/
theorem specialCoordinate_preimage_singleton (i : Fin n) :
    (specialCoordinate n) ⁻¹' {i} = specialCoordinateEvent n i := by
  ext ω
  simp [specialCoordinate, specialCoordinateEvent]

open Classical in
/-- Under the disjoint-conditioned distribution, the event `T = i`, written as a preimage of
the singleton `{i}` under `specialCoordinate`, has the uniform mass `1 / n`. -/
theorem disjointCondMeasure_measureReal_specialCoordinate_preimage_singleton (i : Fin n) :
    (disjointCondMeasure n).real ((specialCoordinate n) ⁻¹' {i}) =
      (1 / (n : ℝ) : ℝ) := by
  rw [specialCoordinate_preimage_singleton,
    disjointCondMeasure_measureReal_specialCoordinateEvent]

/-- Under the measure conditioned on disjointness, almost every sample lies in the disjoint
event `𝒟`. -/
theorem disjointCondMeasure_ae_disjointEvent :
    ∀ᵐ ω ∂disjointCondMeasure n, ω ∈ disjointEvent n := by
  rw [disjointCondMeasure]
  exact ae_cond_mem MeasurableSet.of_discrete

/-- If Bob's special bit `Y_T` is `false`, the generated inputs are disjoint: the sample lies
in `𝒟`. -/
theorem mem_disjointEvent_of_specialY_eq_false
    {ω : HardSample n} (hY : specialY n ω = false) :
    ω ∈ disjointEvent n := by
  change Disjoint (X n ω) (Y n ω)
  rw [disjoint_X_Y_iff]
  intro hboth
  rw [show ω.yT = false by simpa [specialY] using hY] at hboth
  simp at hboth

/-- If a prescribed value `(bx, bY)` of the special bits is not `(true, true)`, then the
event `(X_T, Y_T) = (bx, bY)` is contained in the disjoint event `𝒟`. -/
theorem specialBitsEvent_subset_disjointEvent
    (bx bY : Bool) (hbits : ¬(bx = true ∧ bY = true)) :
    specialBitsEvent n bx bY ⊆ disjointEvent n := by
  intro ω hω
  rw [specialBitsEvent] at hω
  change Disjoint (X n ω) (Y n ω)
  rw [disjoint_X_Y_iff]
  intro hspecial
  exact hbits ⟨hω.1.symm.trans hspecial.1, hω.2.symm.trans hspecial.2⟩

/-- The event `(X_T, Y_T) = (0, 0)` is contained in the disjoint event `𝒟`. -/
theorem specialZeroZero_subset_disjointEvent :
    specialZeroZero n ⊆ disjointEvent n := by
  intro ω hω
  rw [specialZeroZero, specialBitsEvent] at hω
  exact mem_disjointEvent_of_specialY_eq_false n (by simpa [specialY] using hω.2)

/-- Under the disjoint-conditioned hard distribution, the event `(X_T, Y_T) = (0, 0)` has
mass `1 / 3` (it has unconditional mass `1/4` and lies inside `𝒟`, of mass `3/4`). -/
theorem disjointCondMeasure_measureReal_specialZeroZero :
    (disjointCondMeasure n).real (specialZeroZero n) = (1 / 3 : ℝ) := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hinter :
      disjointEvent n ∩ specialZeroZero n = specialZeroZero n := by
    exact Set.inter_eq_right.mpr (specialZeroZero_subset_disjointEvent n)
  rw [hinter]
  rw [show volume.real (disjointEvent n) = (3 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_disjointEvent n]
  rw [show volume.real (specialZeroZero n) = (1 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_specialZeroZero n]
  norm_num

open Classical in
/-- Under the disjoint-conditioned hard distribution, each of the three non-intersecting
values `(0,0)`, `(1,0)`, `(0,1)` of the special bit pair `(X_T, Y_T)` has mass `1 / 3`. -/
theorem disjointCondMeasure_measureReal_specialBitsEvent
    (bx bY : Bool) (hbits : ¬(bx = true ∧ bY = true)) :
    (disjointCondMeasure n).real (specialBitsEvent n bx bY) = (1 / 3 : ℝ) := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hinter :
      disjointEvent n ∩ specialBitsEvent n bx bY = specialBitsEvent n bx bY := by
    exact Set.inter_eq_right.mpr (specialBitsEvent_subset_disjointEvent n bx bY hbits)
  rw [hinter]
  rw [show volume.real (disjointEvent n) = (3 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_disjointEvent n]
  rw [show volume.real (specialBitsEvent n bx bY) = (1 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_specialBitsEvent n bx bY]
  norm_num

/-- Under the disjoint-conditioned hard distribution, Bob's special bit is `0` with
probability `2 / 3`: `p(b_T = 0 | 𝒟) = 2/3` [RY20, Ch. 6, 'p(b_t = 0 | 𝒟) = 2/3']. -/
theorem disjointCondMeasure_measureReal_specialY_false :
    (disjointCondMeasure n).real (((specialY n) ⁻¹' {false}) : Set (HardSample n)) =
      (2 / 3 : ℝ) := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hsubset : ((specialY n) ⁻¹' {false} : Set (HardSample n)) ⊆ disjointEvent n := by
    intro ω hω
    exact mem_disjointEvent_of_specialY_eq_false n (by simpa using hω)
  have hinter :
      disjointEvent n ∩ ((specialY n) ⁻¹' {false} : Set (HardSample n)) =
        (specialY n) ⁻¹' {false} := by
    exact Set.inter_eq_right.mpr hsubset
  rw [hinter]
  rw [show volume.real (disjointEvent n) = (3 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_disjointEvent n]
  rw [show volume.real
      (((specialY n) ⁻¹' {false}) : Set (HardSample n)) = (1 / 2 : ℝ) by
    simpa [Measure.real] using measureReal_specialY_false n]
  norm_num

open Classical in
/-- The disjoint-conditioned hard distribution, further conditioned on Bob's special bit
being `false`: the law `p(· | 𝒟, b_T = 0)` of [RY20, Ch. 6, 'p(b_t = 0 | 𝒟) = 2/3']. This
is the Alice-side conditioning used in the one-bit Pinsker step. -/
noncomputable def disjointSpecialYFalseMeasure : Measure (HardSample n) :=
  (disjointCondMeasure n)[|(specialY n) ⁻¹' {false}]

open Classical in
/-- Conditioning the disjoint law on `Y_T = false` gives a probability measure, since that
event has positive conditional mass `2 / 3`. -/
theorem disjointSpecialYFalseMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (disjointSpecialYFalseMeasure n) := by
  haveI : IsProbabilityMeasure (disjointCondMeasure n) := by
    rw [disjointCondMeasure]
    exact ProbabilityTheory.cond_isProbabilityMeasure (measure_disjointEvent_ne_zero n)
  rw [disjointSpecialYFalseMeasure]
  apply ProbabilityTheory.cond_isProbabilityMeasure
  rw [← MeasureTheory.measureReal_ne_zero_iff]
  rw [disjointCondMeasure_measureReal_specialY_false]
  norm_num

/-- Under the hard distribution conditioned on `𝒟 ∧ Y_T = 0`, Alice's special bit `X_T` is
uniform: each value `b` has mass `1 / 2`.

**Proof sketch.** Step 1: unfold the conditional measure; the mass is the ratio
`p(Y_T = 0 ∧ X_T = b | 𝒟) / p(Y_T = 0 | 𝒟)`, whose denominator is `2 / 3`. Step 2: split on
`b`. For `b = 0` the intersection event is `(X_T, Y_T) = (0, 0)`, of conditional mass
`1 / 3`; for `b = 1` it is `(X_T, Y_T) = (1, 0)`, which is not the intersecting pair and so
also has conditional mass `1 / 3`. In both cases the ratio is `(1/3) / (2/3) = 1/2`. -/
theorem disjointSpecialYFalseMeasure_measureReal_specialX_singleton (b : Bool) :
    (disjointSpecialYFalseMeasure n).real ((specialX n) ⁻¹' {b}) = (1 / 2 : ℝ) := by
  -- Step 1: unfold the conditioning; the denominator is `p(Y_T = 0 | 𝒟) = 2/3`.
  rw [disjointSpecialYFalseMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hden :
      (disjointCondMeasure n).real (((specialY n) ⁻¹' {false}) : Set (HardSample n)) =
        (2 / 3 : ℝ) :=
    disjointCondMeasure_measureReal_specialY_false n
  -- Step 2: in each case identify the numerator event with a bit-pair event of mass `1/3`.
  cases b
  · have hinter :
        (specialY n) ⁻¹' {false} ∩ ((specialX n) ⁻¹' {false}) =
          specialZeroZero n := by
      ext ω
      rcases ω with ⟨T, xT, yT, other⟩
      cases xT <;> cases yT <;> simp [specialX, specialY, specialZeroZero, specialBitsEvent]
    rw [hinter, disjointCondMeasure_measureReal_specialZeroZero, hden]
    norm_num
  · have hinter :
        (specialY n) ⁻¹' {false} ∩ ((specialX n) ⁻¹' {true}) =
          specialBitsEvent n true false := by
      ext ω
      rcases ω with ⟨T, xT, yT, other⟩
      cases xT <;> cases yT <;> simp [specialX, specialY, specialBitsEvent]
    rw [hinter]
    rw [disjointCondMeasure_measureReal_specialBitsEvent]
    · rw [hden]
      norm_num
    · simp

noncomputable instance disjointCondMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (disjointCondMeasure n) := by
  rw [disjointCondMeasure]
  exact ProbabilityTheory.cond_isProbabilityMeasure (measure_disjointEvent_ne_zero n)

open Classical in
/-- Under the disjoint-conditioned distribution, the disjoint model `ω ↦ (T, coords, junk)`
is uniform: every fibre has mass `1 / (n · 3 ^ n · 3)`, the reciprocal of the size of its
codomain. -/
theorem disjointCondMeasure_measureReal_disjointModel_fiber
    (z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate) :
    (disjointCondMeasure n).real ((disjointModel n) ⁻¹' {z}) =
      (1 / ((n : ℝ) * 3 ^ (n : ℕ) * 3) : ℝ) := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hnum :
      volume.real
          (disjointEvent n ∩ (disjointModel n) ⁻¹' {z}) =
        (1 / ((n : ℝ) * 4 * 3 ^ (n : ℕ)) : ℝ) := by
    simpa [Measure.real] using measureReal_disjointEvent_inter_disjointModel_fiber n z
  have hden : volume.real (disjointEvent n) = (3 / 4 : ℝ) := by
    simpa [Measure.real] using measureReal_disjointEvent n
  rw [hnum, hden]
  have hn : (n : ℝ) ≠ 0 := by positivity
  have hpow : (3 ^ (n : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn, hpow]

/-- The triples `(T, coords, junk)` with prescribed first two components `(i, coords)` are
in bijection with the possible values `junk` of the ignored coordinate. -/
private def disjointModelFiberForSpecialCoordinateCoordinateVectorEquiv
    (i : Fin n) (coords : Fin n → DisjointCoordinate) :
    {z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate //
      z.1 = i ∧ z.2.1 = coords} ≃ DisjointCoordinate where
  toFun z := z.1.2.2
  invFun junk := ⟨(i, coords, junk), by simp⟩
  left_inv z := by
    rcases z with ⟨⟨T, coords', junk⟩, h⟩
    simp only at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  right_inv junk := rfl

/-- There are exactly `3` triples `(T, coords, junk)` with prescribed first two components
`(i, coords)`, one for each value of the ignored coordinate `junk`. -/
theorem card_disjointModel_fiber_for_specialCoordinate_coordinateVector
    (i : Fin n) (coords : Fin n → DisjointCoordinate) :
    Fintype.card
        {z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate //
          z.1 = i ∧ z.2.1 = coords} =
      3 := by
  rw [Fintype.card_congr
        (disjointModelFiberForSpecialCoordinateCoordinateVectorEquiv n i coords)]
  exact DisjointCoordinate.card

open Classical in
/-- Under the disjoint-conditioned distribution, the pair `(T, coords)` of the special
coordinate and the generated disjoint coordinate vector is uniform: the event
`T = i ∧ coords = c` has mass `1 / (n · 3 ^ n)` for every `i` and `c`.

**Proof sketch.** Step 1: the event is the preimage under the disjoint model
`ω ↦ (T, coords, junk)` of the set of triples with first two components `(i, c)`, so its
mass is the sum of the fibre masses over those triples
(`FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers`). Step 2: every fibre of the
disjoint model has conditional mass `1 / (n · 3 ^ n · 3)`. Step 3: there are exactly three
such triples, one per value of the ignored coordinate, so the sum is
`3 · 1 / (n · 3 ^ n · 3) = 1 / (n · 3 ^ n)`. -/
theorem disjointCondMeasure_measureReal_specialCoordinate_disjointCoordinateVector_fiber
    (i : Fin n) (coords : Fin n → DisjointCoordinate) :
    (disjointCondMeasure n).real
        (((specialCoordinate n) ⁻¹' {i}) ∩
          ((disjointCoordinateVector n) ⁻¹' {coords})) =
      (1 / (n * 3 ^ (n : ℕ)) : ℝ) := by
  -- Step 1: the event is a preimage under the disjoint model; sum over its fibres.
  have hpre :=
    FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers
      (Ω := HardSample n)
      (α := Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate)
      (disjointCondMeasure n) (disjointModel n) (fun z => z.1 = i ∧ z.2.1 = coords)
  change (disjointCondMeasure n).real
      {ω | (disjointModel n ω).1 = i ∧ (disjointModel n ω).2.1 = coords} =
    (1 / (n * 3 ^ (n : ℕ)) : ℝ)
  rw [hpre]
  -- Step 2: each fibre has the uniform mass.
  have hfiber (z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate) :
      (disjointCondMeasure n).real ((disjointModel n) ⁻¹' {z}) =
        (1 / (n * 3 ^ (n : ℕ) * 3) : ℝ) := by
    exact disjointCondMeasure_measureReal_disjointModel_fiber n z
  simp_rw [hfiber]
  rw [Finset.sum_ite]
  -- Step 3: exactly three triples have first two components `(i, coords)`.
  have hcardFilter :
      (Finset.univ.filter
        (fun z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate =>
          z.1 = i ∧ z.2.1 = coords)).card = 3 := by
    simpa [Fintype.card_subtype] using
      card_disjointModel_fiber_for_specialCoordinate_coordinateVector n i coords
  simp [hcardFilter]

open Classical in
/-- The uniform law on disjoint coordinate vectors `Fin n → DisjointCoordinate` is the
product measure of `n` copies of the uniform law on the three disjoint pairs; this is the
product structure required of `p(ab | 𝒟)` by the hypothesis of the chain-rule lemma
[RY20, Lemma 6.15 hypothesis] (the pairs `(X_i, Y_i)` are mutually independent under `𝒟`).
-/
theorem uniformDisjointCoordinateVector_eq_pi :
    uniformDisjointCoordinateVector n =
      Measure.pi
        (fun _ : Fin n => uniformDisjointCoordinate) := by
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro coords
  rw [uniformDisjointCoordinateVector_singleton]
  rw [Measure.real, ← Set.univ_pi_singleton, Measure.pi_pi, ENNReal.toReal_prod]
  change (1 / 3 ^ (n : ℕ) : ℝ) =
    ∏ i : Fin n,
      uniformDisjointCoordinate.real {coords i}
  simp_rw [uniformDisjointCoordinate_singleton]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp [one_div, inv_pow]

/-- Under the uniform disjoint-coordinate-vector law, the coordinate projections
`coords ↦ coords i` are mutually independent; this is the hypothesis of the chain-rule lemma
[RY20, Lemma 6.15 hypothesis] (the pairs `(X_i, Y_i)` are mutually independent under `𝒟`).
-/
theorem uniformDisjointCoordinateVector_iIndepFun :
    iIndepFun (fun i (coords : Fin n → DisjointCoordinate) => coords i)
      (uniformDisjointCoordinateVector n) := by
  rw [uniformDisjointCoordinateVector_eq_pi]
  exact iIndepFun_pi (fun _ => aemeasurable_id)

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
