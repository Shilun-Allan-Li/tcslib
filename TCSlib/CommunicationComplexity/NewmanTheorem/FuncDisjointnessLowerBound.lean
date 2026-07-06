/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.FuncDisjointness
import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import TCSlib.CommunicationComplexity.DeterministicCC.Transcript
import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy
import TCSlib.CommunicationComplexity.NewmanTheorem.Pinsker
import TCSlib.CommunicationComplexity.NewmanTheorem.TVDistance
import TCSlib.CommunicationComplexity.NewmanTheorem.KLDivergence
import TCSlib.CommunicationComplexity.NewmanTheorem.Minimax
import Mathlib.Probability.UniformOn
import PFR.Kullback

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Randomized Communication Complexity Lower Bound for Disjointness

## Main results

- `floor_div_pow_lt_publicCoin_communicationComplexity_disjointness`: The randomized public-coin
  communication complexity of disjointness on `n`-element sets is at least `n / 2^32`, establishing
  a linear lower bound at fixed error `1/32`.
- `lt_publicCoin_communicationComplexity_disjointness_of_lt_const_mul_n`: Any protocol of
  complexity `< c * n` fails with error `> 1/32` under the hard distribution.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
- Adapted from Chapter 6 of *Communication Complexity* by Rao and Yehudayoff
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Functions.Disjointness

namespace RandomizedLowerBound

variable (n : ℕ+)

noncomputable instance setFinFiniteMeasureSpace :
    FiniteMeasureSpace (Set (Fin n)) :=
  FiniteMeasureSpace.of (Set (Fin n))

/-- The three possible disjoint coordinate-pairs used away from the special coordinate. -/
inductive DisjointCoordinate
  | neither
  | leftOnly
  | rightOnly
  deriving DecidableEq, Fintype

instance disjointCoordinateNonempty : Nonempty DisjointCoordinate :=
  ⟨DisjointCoordinate.neither⟩

instance disjointCoordinateMeasurableSpace : MeasurableSpace DisjointCoordinate := ⊤

instance disjointCoordinateDiscreteMeasurableSpace :
    DiscreteMeasurableSpace DisjointCoordinate := by
  infer_instance

instance disjointCoordinateFiniteMeasureSpace : FiniteMeasureSpace DisjointCoordinate :=
  FiniteMeasureSpace.of DisjointCoordinate

namespace DisjointCoordinate

/-- Alice's bit in a disjoint coordinate-pair. -/
def xBit : DisjointCoordinate → Bool
  | neither => false
  | leftOnly => true
  | rightOnly => false

/-- Bob's bit in a disjoint coordinate-pair. -/
def yBit : DisjointCoordinate → Bool
  | neither => false
  | leftOnly => false
  | rightOnly => true

/-- There are three disjoint coordinate-pairs. -/
theorem card :
    Fintype.card DisjointCoordinate = 3 := by
  decide

/-- A disjoint coordinate-pair never has both bits equal to `true`. -/
theorem not_xBit_and_yBit (c : DisjointCoordinate) :
    ¬(xBit c = true ∧ yBit c = true) := by
  cases c <;> simp [xBit, yBit]

/-- Swap Alice's and Bob's sides in a disjoint coordinate. -/
def swap : DisjointCoordinate → DisjointCoordinate
  | neither => neither
  | leftOnly => rightOnly
  | rightOnly => leftOnly

/-- Swapping sides twice recovers the original disjoint coordinate. -/
theorem swap_swap (c : DisjointCoordinate) :
    swap (swap c) = c := by
  cases c <;> rfl

/-- After swapping a disjoint coordinate, Alice sees Bob's original bit. -/
theorem xBit_swap (c : DisjointCoordinate) :
    xBit (swap c) = yBit c := by
  cases c <;> rfl

end DisjointCoordinate

/-- The sample space for the hard distribution.  The `other` coordinate at `T` is ignored; keeping
it in the sample space makes the ambient type a simple product-like finite type. -/
structure HardSample where
  T : Fin n
  xT : Bool
  yT : Bool
  other : Fin n → DisjointCoordinate
  deriving DecidableEq, Fintype

namespace HardSample

instance : Nonempty (HardSample n) :=
  ⟨{ T := ⟨0, n.pos⟩
     xT := false
     yT := false
     other := fun _ => DisjointCoordinate.neither }⟩

instance : MeasurableSpace (HardSample n) := ⊤

/-- We use the uniform distribution on the explicit hard-distribution sample space. -/
noncomputable instance measureSpace : MeasureSpace (HardSample n) :=
  ⟨ProbabilityTheory.uniformOn Set.univ⟩

noncomputable instance isProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure (HardSample n)) := by
  change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
  infer_instance

noncomputable instance finiteProbabilitySpace : FiniteProbabilitySpace (HardSample n) :=
  FiniteProbabilitySpace.of (HardSample n)

def equivProd :
    HardSample n ≃ Fin n × Bool × Bool × (Fin n → DisjointCoordinate) where
  toFun ω := (ω.T, ω.xT, ω.yT, ω.other)
  invFun p :=
    { T := p.1
      xT := p.2.1
      yT := p.2.2.1
      other := p.2.2.2 }
  left_inv ω := by
    rcases ω with ⟨T, xT, yT, other⟩
    rfl
  right_inv p := by
    rcases p with ⟨T, xT, yT, other⟩
    rfl

/-- Cardinality of the explicit hard-distribution sample space. -/
theorem card :
    Fintype.card (HardSample n) = (n : ℕ) * 4 * 3 ^ (n : ℕ) := by
  calc
    Fintype.card (HardSample n) =
        Fintype.card (Fin n × Bool × Bool × (Fin n → DisjointCoordinate)) :=
      Fintype.card_congr (equivProd n)
    _ = (n : ℕ) * 4 * 3 ^ (n : ℕ) := by
      simp [Fintype.card_prod, Fintype.card_pi, DisjointCoordinate.card]
      ring

end HardSample

/-- Uniform law on the special coordinate. -/
noncomputable def uniformFin : Measure (Fin n) :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable instance uniformFin_isProbabilityMeasure :
    IsProbabilityMeasure (uniformFin n) := by
  rw [uniformFin]
  infer_instance

/-- Each coordinate has mass `1 / n` under the uniform law on `Fin n`. -/
theorem uniformFin_singleton (i : Fin n) :
    (uniformFin n).real {i} =
      (1 / (n : ℝ) : ℝ) := by
  rw [uniformFin]
  rw [Measure.real, ProbabilityTheory.uniformOn_univ]
  simp

open Classical in
/-- The uniform law on `Fin n` assigns mass by normalized cardinality. -/
theorem uniformFin_real (S : Set (Fin n)) :
    (uniformFin n).real S =
      (Fintype.card {i : Fin n // i ∈ S} : ℝ) / (n : ℝ) := by
  rw [uniformFin]
  rw [Measure.real, uniformOn_univ_measureReal_eq_card_subtype]
  simp

/-- The uniform law on `Fin n` has total mass `1`. -/
theorem uniformFin_univ :
    (uniformFin n).real Set.univ = 1 := by
  rw [uniformFin_real]
  simp

/-- Uniform law on one bit. -/
noncomputable def uniformBool : Measure Bool :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable instance uniformBool_isProbabilityMeasure :
    IsProbabilityMeasure uniformBool := by
  rw [uniformBool]
  infer_instance

/-- Each bit has mass `1 / 2` under the uniform law on one bit. -/
theorem uniformBool_singleton (b : Bool) :
    uniformBool.real {b} =
      (1 / 2 : ℝ) := by
  rw [uniformBool]
  rw [Measure.real, ProbabilityTheory.uniformOn_univ]
  norm_num

open Classical in
/-- The uniform law on `Bool` assigns mass by normalized cardinality. -/
theorem uniformBool_real (S : Set Bool) :
    uniformBool.real S =
      (Fintype.card {b : Bool // b ∈ S} : ℝ) / 2 := by
  rw [uniformBool]
  rw [Measure.real, uniformOn_univ_measureReal_eq_card_subtype]
  norm_num

/-- The uniform law on `Bool` has total mass `1`. -/
theorem uniformBool_univ :
    uniformBool.real Set.univ = 1 := by
  rw [uniformBool_real]
  norm_num

/-- The uniform law on generated disjoint coordinate vectors. -/
noncomputable def uniformDisjointCoordinateVector :
    Measure (Fin n → DisjointCoordinate) :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable instance uniformDisjointCoordinateVector_isProbabilityMeasure :
    IsProbabilityMeasure (uniformDisjointCoordinateVector n) := by
  rw [uniformDisjointCoordinateVector]
  infer_instance

/-- The uniform law on one disjoint coordinate. -/
noncomputable def uniformDisjointCoordinate :
    Measure DisjointCoordinate :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable instance uniformDisjointCoordinate_isProbabilityMeasure :
    IsProbabilityMeasure uniformDisjointCoordinate := by
  rw [uniformDisjointCoordinate]
  infer_instance

open Classical in
/-- Each generated disjoint coordinate vector has mass `3^{-n}` under the uniform law. -/
theorem uniformDisjointCoordinateVector_singleton
    (coords : Fin n → DisjointCoordinate) :
    (uniformDisjointCoordinateVector n).real {coords} =
      (1 / (3 ^ (n : ℕ)) : ℝ) := by
  rw [uniformDisjointCoordinateVector]
  change ((ProbabilityTheory.uniformOn Set.univ :
      Measure (Fin n → DisjointCoordinate)) ({coords} : Set (Fin n → DisjointCoordinate))).toReal =
    (1 / (3 ^ (n : ℕ)) : ℝ)
  rw [uniformOn_univ_measureReal_eq_card_subtype]
  have hcard :
      Fintype.card {x : Fin n → DisjointCoordinate // x ∈ ({coords} : Set _)} = 1 := by
    let e : {x : Fin n → DisjointCoordinate // x ∈ ({coords} : Set _)} ≃ Unit := {
      toFun _ := Unit.unit
      invFun _ := ⟨coords, by simp⟩
      left_inv x := by
        apply Subtype.ext
        simpa using x.2.symm
      right_inv _ := rfl }
    calc
      Fintype.card {x : Fin n → DisjointCoordinate // x ∈ ({coords} : Set _)} =
          Fintype.card Unit :=
        Fintype.card_congr e
      _ = 1 := by simp
  rw [hcard]
  simp [Fintype.card_pi, DisjointCoordinate.card]

open Classical in
/-- The uniform law on disjoint-coordinate vectors assigns mass by normalized cardinality. -/
theorem uniformDisjointCoordinateVector_real
    (S : Set (Fin n → DisjointCoordinate)) :
    (uniformDisjointCoordinateVector n).real S =
      (Fintype.card {coords : Fin n → DisjointCoordinate // coords ∈ S} : ℝ) /
        (3 ^ (n : ℕ) : ℝ) := by
  rw [uniformDisjointCoordinateVector]
  rw [Measure.real, uniformOn_univ_measureReal_eq_card_subtype]
  simp [Fintype.card_pi, DisjointCoordinate.card]

/-- The uniform law on disjoint-coordinate vectors has total mass `1`. -/
theorem uniformDisjointCoordinateVector_univ :
    (uniformDisjointCoordinateVector n).real Set.univ = 1 := by
  rw [uniformDisjointCoordinateVector_real]
  simp [Fintype.card_pi, DisjointCoordinate.card]

open Classical in
/-- Each disjoint coordinate has mass `1 / 3` under the one-coordinate uniform law. -/
theorem uniformDisjointCoordinate_singleton (c : DisjointCoordinate) :
    uniformDisjointCoordinate.real {c} = (1 / 3 : ℝ) := by
  rw [uniformDisjointCoordinate]
  change ((ProbabilityTheory.uniformOn Set.univ :
      Measure DisjointCoordinate) ({c} : Set DisjointCoordinate)).toReal = (1 / 3 : ℝ)
  rw [uniformOn_univ_measureReal_eq_card_subtype]
  have hcard :
      Fintype.card {x : DisjointCoordinate // x ∈ ({c} : Set DisjointCoordinate)} = 1 := by
    let e : {x : DisjointCoordinate // x ∈ ({c} : Set DisjointCoordinate)} ≃ Unit := {
      toFun _ := Unit.unit
      invFun _ := ⟨c, by simp⟩
      left_inv x := by
        apply Subtype.ext
        simpa using x.2.symm
      right_inv _ := rfl }
    calc
      Fintype.card {x : DisjointCoordinate // x ∈ ({c} : Set DisjointCoordinate)} =
          Fintype.card Unit :=
        Fintype.card_congr e
      _ = 1 := by simp
  rw [hcard]
  simp [DisjointCoordinate.card]

/-- Alice's bit at coordinate `i` under a hard-distribution sample. -/
def xBit (ω : HardSample n) (i : Fin n) : Bool :=
  if i = ω.T then ω.xT else (ω.other i).xBit

/-- Bob's bit at coordinate `i` under a hard-distribution sample. -/
def yBit (ω : HardSample n) (i : Fin n) : Bool :=
  if i = ω.T then ω.yT else (ω.other i).yBit

/-- Alice's input set under a hard-distribution sample. -/
def X (ω : HardSample n) : Set (Fin n) :=
  {i | xBit n ω i = true}

/-- Bob's input set under a hard-distribution sample. -/
def Y (ω : HardSample n) : Set (Fin n) :=
  {i | yBit n ω i = true}

/-- Alice's full input vector under a hard-distribution sample. -/
def xVector (ω : HardSample n) : Fin n → Bool :=
  xBit n ω

/-- Bob's full input vector under a hard-distribution sample. -/
def yVector (ω : HardSample n) : Fin n → Bool :=
  yBit n ω

/-- Reverse the coordinate order of a boolean vector. -/
def reverseBoolVector (v : Fin n → Bool) : Fin n → Bool :=
  v ∘ Fin.rev

/-- Reversing a boolean vector twice recovers it. -/
theorem reverseBoolVector_reverseBoolVector (v : Fin n → Bool) :
    reverseBoolVector n (reverseBoolVector n v) = v := by
  funext i
  simp [reverseBoolVector]

/-- Reversing boolean vectors is injective. -/
theorem reverseBoolVector_injective :
    Function.Injective (reverseBoolVector n) := by
  intro v w h
  have h' := congrArg (reverseBoolVector n) h
  simpa [reverseBoolVector_reverseBoolVector] using h'

/-- Reverse the coordinate order of a subset of coordinates. -/
def reverseSet (S : Set (Fin n)) : Set (Fin n) :=
  {i | Fin.rev i ∈ S}

/-- Reversing a coordinate set twice recovers it. -/
theorem reverseSet_reverseSet (S : Set (Fin n)) :
    reverseSet n (reverseSet n S) = S := by
  ext i
  simp [reverseSet]

/-- The input pair generated by a hard-distribution sample. -/
def input (ω : HardSample n) : Set (Fin n) × Set (Fin n) :=
  (X n ω, Y n ω)

/-- The event that the special coordinate is an actual intersection. -/
def specialIntersect : Set (HardSample n) :=
  {ω | ω.xT = true ∧ ω.yT = true}

/-- The event that the two special-coordinate bits have prescribed values. -/
def specialBitsEvent (bx bY : Bool) : Set (HardSample n) :=
  {ω | ω.xT = bx ∧ ω.yT = bY}

/-- The event that the special coordinate has a prescribed value. -/
def specialCoordinateEvent (i : Fin n) : Set (HardSample n) :=
  {ω | ω.T = i}

/-- The event that both special-coordinate bits are zero. -/
def specialZeroZero : Set (HardSample n) :=
  specialBitsEvent n false false

/-- The event that the generated input pair is disjoint. -/
def disjointEvent : Set (HardSample n) :=
  {ω | Disjoint (X n ω) (Y n ω)}

noncomputable instance specialIntersectFintype :
    Fintype {ω : HardSample n // ω ∈ specialIntersect n} := by
  unfold specialIntersect
  infer_instance

noncomputable instance specialBitsEventFintype (bx bY : Bool) :
    Fintype {ω : HardSample n // ω ∈ specialBitsEvent n bx bY} := by
  unfold specialBitsEvent
  infer_instance

noncomputable instance specialCoordinateEventFintype (i : Fin n) :
    Fintype {ω : HardSample n // ω ∈ specialCoordinateEvent n i} := by
  unfold specialCoordinateEvent
  infer_instance

/-- The special coordinate selected by the hard distribution. -/
def specialCoordinate (ω : HardSample n) : Fin n :=
  ω.T

/-- Alice's bit at the special coordinate. -/
def specialX (ω : HardSample n) : Bool :=
  ω.xT

/-- Bob's bit at the special coordinate. -/
def specialY (ω : HardSample n) : Bool :=
  ω.yT

/-- Alice's input bits before the special coordinate, padded by `false` elsewhere. -/
def xBeforeSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if i < ω.T then xBit n ω i else false

/-- Alice's input bits up to and including the special coordinate, padded by `false` elsewhere. -/
def xLeSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if i ≤ ω.T then xBit n ω i else false

/-- Bob's input bits after the special coordinate, padded by `false` elsewhere. -/
def yAfterSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if ω.T < i then yBit n ω i else false

/-- Bob's input bits from the special coordinate onward, padded by `false` elsewhere. -/
def yGeSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if ω.T ≤ i then yBit n ω i else false

/-- The common coarse variable `T, X_<T, Y_>T` used for special-coordinate fibers. -/
def coarseConditioning (ω : HardSample n) :
    Fin n × (Fin n → Bool) × (Fin n → Bool) :=
  (specialCoordinate n ω, xBeforeSpecial n ω, yAfterSpecial n ω)

/-- Alice's corrected special-coordinate conditioning variable: `T, X_<T, Y_≥T`. -/
def aliceClaimConditioning (ω : HardSample n) :
    Fin n × (Fin n → Bool) × (Fin n → Bool) :=
  (specialCoordinate n ω, xBeforeSpecial n ω, yGeSpecial n ω)

/-- Alice's corrected conditioning data without the special coordinate:
`X_<T, Y_≥T`. -/
def aliceDynamicConditioning (ω : HardSample n) :
    (Fin n → Bool) × (Fin n → Bool) :=
  (xBeforeSpecial n ω, yGeSpecial n ω)

/-- Alice's corrected conditioning is the special coordinate together with the remaining
conditioning data. -/
theorem aliceClaimConditioning_eq_specialCoordinate_prod_dynamic :
    aliceClaimConditioning n =
      fun ω => (specialCoordinate n ω, aliceDynamicConditioning n ω) := by
  rfl

/-- Bob's corrected special-coordinate conditioning variable: `T, X_≤T, Y_>T`. -/
def bobClaimConditioning (ω : HardSample n) :
    Fin n × (Fin n → Bool) × (Fin n → Bool) :=
  (specialCoordinate n ω, xLeSpecial n ω, yAfterSpecial n ω)

/-- Alice's bit at a fixed coordinate. -/
def fixedXBit (i : Fin n) (ω : HardSample n) : Bool :=
  xBit n ω i

/-- Alice's fixed-coordinate strict prefix `X_<i`, represented without padding. -/
def fixedXStrictPrefix (i : Fin n) (ω : HardSample n) : Fin i.1 → Bool :=
  fun j => xBit n ω ⟨j.1, lt_trans j.2 i.2⟩

/-- Alice's fixed-coordinate `X_<i` prefix. -/
def fixedXBefore (i : Fin n) (ω : HardSample n) : Fin n → Bool :=
  fun j => if j < i then xBit n ω j else false

/-- Bob's fixed-coordinate `Y_<i` prefix. -/
def fixedYBefore (i : Fin n) (ω : HardSample n) : Fin n → Bool :=
  fun j => if j < i then yBit n ω j else false

/-- Bob's fixed-coordinate `Y_≥i` suffix. -/
def fixedYGe (i : Fin n) (ω : HardSample n) : Fin n → Bool :=
  fun j => if i ≤ j then yBit n ω j else false

/-- The fixed-coordinate Alice conditioning variable `X_<i, Y_≥i`. -/
def fixedAliceConditioning (i : Fin n) (ω : HardSample n) :
    (Fin n → Bool) × (Fin n → Bool) :=
  (fixedXBefore n i ω, fixedYGe n i ω)

/-- The fixed-coordinate conditioning variable `(X_<i, Y)` used in the chain-rule sum.
The `X_<i` prefix is represented without padding so that recodings are injective. -/
def fixedAliceFullYConditioning (i : Fin n) (ω : HardSample n) :
    (Fin i.1 → Bool) × (Fin n → Bool) :=
  (fixedXStrictPrefix n i ω, yVector n ω)

/-- Recode `(X_<i, Y)` as `(Y_<i, X_<i, Y_≥i)`, the conditioning variable produced by
the chain-rule split. -/
def fixedAliceChainConditioningValue (i : Fin n)
    (c : (Fin i.1 → Bool) × (Fin n → Bool)) :
    (Fin n → Bool) × ((Fin n → Bool) × (Fin n → Bool)) :=
  (fun j => if j < i then c.2 j else false,
    (fun j => if h : j < i then c.1 ⟨j.1, h⟩ else false,
      fun j => if i ≤ j then c.2 j else false))

/-- The chain-rule conditioning `(Y_<i, X_<i, Y_≥i)` is an injective recoding of `(X_<i, Y)`. -/
theorem fixedAliceChainConditioningValue_injective (i : Fin n) :
    Function.Injective (fixedAliceChainConditioningValue n i) := by
  intro a b h
  ext j
  · let j' : Fin n := ⟨j.1, lt_trans j.2 i.2⟩
    have hlt : j' < i := j.2
    have hx := congr_fun (congrArg (fun c => c.2.1) h) j'
    simpa [fixedAliceChainConditioningValue, j', hlt] using hx
  · by_cases hj : j < i
    · have hy := congr_fun (congrArg Prod.fst h) j
      simpa [fixedAliceChainConditioningValue, hj] using hy
    · have hge : i ≤ j := le_of_not_gt hj
      have hy := congr_fun (congrArg (fun c => c.2.2) h) j
      simpa [fixedAliceChainConditioningValue, hj, hge] using hy

/-- On hard samples, recoding `(X_<i, Y)` gives exactly `(Y_<i, X_<i, Y_≥i)`. -/
theorem fixedAliceChainConditioningValue_fixedAliceFullYConditioning (i : Fin n) :
    fixedAliceChainConditioningValue n i ∘ fixedAliceFullYConditioning n i =
      fun ω => (fixedYBefore n i ω, fixedAliceConditioning n i ω) := by
  funext ω
  ext j <;>
    simp [fixedAliceChainConditioningValue, fixedAliceFullYConditioning,
      fixedXStrictPrefix, fixedYBefore, fixedAliceConditioning, fixedXBefore, fixedYGe,
      yVector]

/-- The values of Alice's corrected conditioning variable for which `Y_T = false`. -/
def aliceClaimConditioningYFalseValues :
    Set (Fin n × (Fin n → Bool) × (Fin n → Bool)) :=
  {c | c.2.2 c.1 = false}

/-- The `Y_≥T` component of Alice's corrected conditioning contains the bit `Y_T`. -/
theorem yGeSpecial_specialCoordinate (ω : HardSample n) :
    yGeSpecial n ω (specialCoordinate n ω) = specialY n ω := by
  simp [yGeSpecial, specialCoordinate, specialY, yBit]

/-- The event `Y_T=false` is determined by Alice's corrected conditioning variable. -/
theorem specialY_false_eq_preimage_aliceClaimConditioningYFalseValues :
    (((specialY n) ⁻¹' {false}) : Set (HardSample n)) =
      (aliceClaimConditioning n) ⁻¹' aliceClaimConditioningYFalseValues n := by
  ext ω
  simp [aliceClaimConditioningYFalseValues, aliceClaimConditioning,
    yGeSpecial_specialCoordinate]

/-- The conditioning-value recoding induced by reversing coordinates and swapping Alice/Bob. -/
def dualConditioningValue
    (c : Fin n × (Fin n → Bool) × (Fin n → Bool)) :
    Fin n × (Fin n → Bool) × (Fin n → Bool) :=
  (Fin.rev c.1, reverseBoolVector n c.2.2, reverseBoolVector n c.2.1)

/-- Recoding a conditioning value twice recovers the original value. -/
theorem dualConditioningValue_dualConditioningValue
    (c : Fin n × (Fin n → Bool) × (Fin n → Bool)) :
    dualConditioningValue n (dualConditioningValue n c) = c := by
  rcases c with ⟨i, x, y⟩
  simp [dualConditioningValue, reverseBoolVector_reverseBoolVector]

/-- The conditioning-value duality map is injective. -/
theorem dualConditioningValue_injective :
    Function.Injective (dualConditioningValue n) := by
  intro c c' h
  have h' := congrArg (dualConditioningValue n) h
  simpa [dualConditioningValue_dualConditioningValue] using h'

/-- The deterministic protocol type for disjointness inputs of length `n`. -/
abbrev ProtocolType : Type :=
  Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool

/-- The syntactic transcript type for a disjointness protocol. -/
abbrev TranscriptType
    (p : ProtocolType n) : Type :=
  Deterministic.Protocol.Transcript p

/-- The raw type of values of the `Z = (M, T, X_<T, Y_>T)` variable for a protocol. -/
structure RawZType
    (p : ProtocolType n) where
  transcript : TranscriptType n p
  specialCoordinate : Fin n
  xBefore : Fin n → Bool
  yAfter : Fin n → Bool

namespace RawZType

variable {p : ProtocolType n}

@[ext]
theorem ext
    {z z' : RawZType n p}
    (htranscript : z.transcript = z'.transcript)
    (hT : z.specialCoordinate = z'.specialCoordinate)
    (hxBefore : z.xBefore = z'.xBefore)
    (hyAfter : z.yAfter = z'.yAfter) :
    z = z' := by
  rcases z with ⟨m, T, x, y⟩
  rcases z' with ⟨m', T', x', y'⟩
  change m = m' at htranscript
  change T = T' at hT
  change x = x' at hxBefore
  change y = y' at hyAfter
  subst m'
  subst T'
  subst x'
  subst y'
  rfl

/-- A raw `Z` value is equivalent to the product of its named fields. -/
def equivProd
    (p : ProtocolType n) :
    RawZType n p ≃ TranscriptType n p × Fin n × (Fin n → Bool) × (Fin n → Bool) where
  toFun z := (z.transcript, z.specialCoordinate, z.xBefore, z.yAfter)
  invFun z :=
    { transcript := z.1
      specialCoordinate := z.2.1
      xBefore := z.2.2.1
      yAfter := z.2.2.2 }
  left_inv z := by
    cases z
    rfl
  right_inv z := by
    rcases z with ⟨transcript, specialCoordinate, xBefore, yAfter⟩
    rfl

end RawZType

open Classical in
noncomputable instance rawZTypeFintype (p : ProtocolType n) : Fintype (RawZType n p) :=
  Fintype.ofEquiv
    (TranscriptType n p × Fin n × (Fin n → Bool) × (Fin n → Bool))
    (RawZType.equivProd n p).symm

open Classical in
noncomputable instance rawZTypeDecidableEq (p : ProtocolType n) : DecidableEq (RawZType n p) :=
  Classical.decEq _

/-- The raw `Z = (M, T, X_<T, Y_>T)` variable used for coarse special-coordinate fibers. -/
noncomputable def rawZVariable
    (p : ProtocolType n)
    (ω : HardSample n) : RawZType n p :=
  { transcript := p.transcript (input n ω)
    specialCoordinate := specialCoordinate n ω
    xBefore := xBeforeSpecial n ω
    yAfter := yAfterSpecial n ω }

/-- The type of achievable values of the `Z = (M, T, X_<T, Y_>T)` variable for a protocol. -/
abbrev ZType
    (p : ProtocolType n) : Type :=
  {z : RawZType n p // ∃ ω : HardSample n, rawZVariable n p ω = z}

namespace ZType

variable {p : ProtocolType n}

/-- The transcript component of an achievable `Z` value. -/
def transcript
    (z : ZType n p) : TranscriptType n p :=
  z.1.transcript

/-- The special-coordinate component of an achievable `Z` value. -/
def specialCoordinate
    (z : ZType n p) : Fin n :=
  z.1.specialCoordinate

/-- The `X_<T` component of an achievable `Z` value. -/
def xBefore
    (z : ZType n p) : Fin n → Bool :=
  z.1.xBefore

/-- The `Y_>T` component of an achievable `Z` value. -/
def yAfter
    (z : ZType n p) : Fin n → Bool :=
  z.1.yAfter

/-- The raw value underlying an achievable `Z` value. -/
def raw
    (z : ZType n p) : RawZType n p :=
  z.1

/-- The achievability proof carried by a `ZType` value. -/
theorem achievable
    (z : ZType n p) :
    ∃ ω : HardSample n, rawZVariable n p ω = z.raw :=
  z.2

@[ext]
theorem ext
    {z z' : ZType n p}
    (htranscript : z.transcript = z'.transcript)
    (hT : z.specialCoordinate = z'.specialCoordinate)
    (hxBefore : z.xBefore = z'.xBefore)
    (hyAfter : z.yAfter = z'.yAfter) :
    z = z' := by
  apply Subtype.ext
  exact RawZType.ext (n := n) (p := p) htranscript hT hxBefore hyAfter

end ZType

open Classical in
noncomputable instance zTypeFintype (p : ProtocolType n) : Fintype (ZType n p) := by
  unfold ZType
  infer_instance

instance zTypeMeasurableSpace (p : ProtocolType n) : MeasurableSpace (ZType n p) := ⊤

/-- The `Z = (M, T, X_<T, Y_>T)` variable used for coarse special-coordinate fibers. -/
noncomputable def zVariable
    (p : ProtocolType n)
    (ω : HardSample n) : ZType n p :=
  ⟨rawZVariable n p ω, ⟨ω, rfl⟩⟩

/-- The fiber of the `Z = (M, T, X_<T, Y_>T)` variable above a value `z`. -/
def zFiber
    (p : ProtocolType n)
    (z : ZType n p) : Set (HardSample n) :=
  (zVariable n p) ⁻¹' {z}

/-- The protocol output determined by a `Z` value, through its transcript leaf. -/
noncomputable def zOutput
    (p : ProtocolType n)
    (z : ZType n p) : Bool :=
  Deterministic.Protocol.Transcript.output z.transcript

theorem run_eq_zOutput_of_zVariable_eq
    (p : ProtocolType n)
    {z : ZType n p} {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    p.run (X n ω) (Y n ω) = zOutput n p z := by
  simpa [zOutput, input] using
    (Deterministic.Protocol.run_eq_transcript_output p (input n ω)).trans
      (congrArg Deterministic.Protocol.Transcript.output
        (congrArg (fun z : ZType n p => z.transcript) hω))

open Classical in
/-- Every achievable `Z` fiber has positive ambient hard-distribution mass. -/
theorem volume_zFiber_ne_zero
    (p : ProtocolType n)
    (z : ZType n p) :
    volume (zFiber n p z) ≠ 0 := by
  rcases z.achievable with ⟨ω, hω⟩
  have hzω : zVariable n p ω = z := by
    apply Subtype.ext
    simpa [ZType.raw, zVariable] using hω
  rw [← MeasureTheory.measureReal_ne_zero_iff]
  rw [zFiber]
  rw [Measure.real]
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n))
    ((zVariable n p) ⁻¹' {z})).toReal ≠ 0
  rw [uniformOn_univ_measureReal_eq_card_subtype]
  apply ne_of_gt
  apply div_pos
  · have hsub_nonempty :
        Nonempty {η : HardSample n // η ∈ (zVariable n p) ⁻¹' {z}} :=
      ⟨⟨ω, by simpa using hzω⟩⟩
    exact_mod_cast Fintype.card_pos_iff.mpr hsub_nonempty
  · exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (HardSample n))

/-- The hard input distribution as a measure on input pairs. -/
noncomputable def inputMeasure :
    Measure (Set (Fin n) × Set (Fin n)) :=
  Measure.map (input n) volume

noncomputable instance inputMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (inputMeasure n) := by
  rw [inputMeasure]
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable (f := input n))

/-- The hard input distribution packaged as a finite probability space for distributional error. -/
noncomputable def inputDist :
    FiniteProbabilitySpace (Set (Fin n) × Set (Fin n)) :=
  FiniteProbabilitySpace.ofMeasure
    (Set (Fin n) × Set (Fin n)) (inputMeasure n)

/-- The protocol dual swaps Alice/Bob and reverses both coordinate sets. -/
def dualProtocol
    (p : ProtocolType n) :
    ProtocolType n :=
  p.swap.comap (reverseSet n) (reverseSet n)

/-- The transcript-level map induced by protocol duality. -/
def dualProtocolTranscriptMap
    (p : ProtocolType n) :
    TranscriptType n p → TranscriptType n (dualProtocol n p) :=
  fun transcript =>
    Deterministic.Protocol.transcriptComap p.swap (reverseSet n) (reverseSet n)
      (Deterministic.Protocol.transcriptSwap transcript)

/-- The transcript-level map induced by protocol duality is injective. -/
theorem dualProtocolTranscriptMap_injective
    (p : ProtocolType n) :
    Function.Injective (dualProtocolTranscriptMap n p) := by
  exact
    (Deterministic.Protocol.transcriptComap_injective p.swap (reverseSet n) (reverseSet n)).comp
      (Deterministic.Protocol.transcriptSwap_injective p)

theorem xBit_of_ne_special (ω : HardSample n) {i : Fin n} (hi : i ≠ ω.T) :
    xBit n ω i = (ω.other i).xBit := by
  simp [xBit, hi]

theorem yBit_of_ne_special (ω : HardSample n) {i : Fin n} (hi : i ≠ ω.T) :
    yBit n ω i = (ω.other i).yBit := by
  simp [yBit, hi]

/-- Away from `T`, generated coordinate-pairs are disjoint. -/
theorem not_xBit_and_yBit_of_ne_special
    (ω : HardSample n) {i : Fin n} (hi : i ≠ ω.T) :
    ¬(xBit n ω i = true ∧ yBit n ω i = true) := by
  rw [xBit_of_ne_special n ω hi, yBit_of_ne_special n ω hi]
  exact DisjointCoordinate.not_xBit_and_yBit (ω.other i)

/-- The disjoint coordinate with the given bits. On the invalid `(true, true)` input this chooses
an arbitrary disjoint coordinate; the projection lemmas below assume that invalid case away. -/
def coordinateOfBits (x y : Bool) : DisjointCoordinate :=
  if x = true then DisjointCoordinate.leftOnly
  else if y = true then DisjointCoordinate.rightOnly
  else DisjointCoordinate.neither

/-- `coordinateOfBits` preserves Alice's bit when the requested pair is disjoint. -/
theorem coordinateOfBits_xBit {x y : Bool} (h : ¬(x = true ∧ y = true)) :
    (coordinateOfBits x y).xBit = x := by
  cases x <;> cases y <;> simp [coordinateOfBits, DisjointCoordinate.xBit] at h ⊢

/-- `coordinateOfBits` preserves Bob's bit when the requested pair is disjoint. -/
theorem coordinateOfBits_yBit {x y : Bool} (h : ¬(x = true ∧ y = true)) :
    (coordinateOfBits x y).yBit = y := by
  cases x <;> cases y <;> simp [coordinateOfBits, DisjointCoordinate.yBit] at h ⊢

/-- `coordinateOfBits` reconstructs an existing disjoint coordinate from its two projections. -/
theorem coordinateOfBits_xBit_yBit (c : DisjointCoordinate) :
    coordinateOfBits c.xBit c.yBit = c := by
  cases c <;> simp [coordinateOfBits, DisjointCoordinate.xBit, DisjointCoordinate.yBit]

/-- Mix Alice's input from `ωX` with Bob's input from `ωY`. This is only intended to be used
when the two samples agree on `T`, `X_<T`, and `Y_>T`; under those hypotheses the mixed
coordinate requests are always disjoint. -/
def mix (ωX ωY : HardSample n) : HardSample n where
  T := ωX.T
  xT := ωX.xT
  yT := ωY.yT
  other := fun i =>
    if i = ωX.T then ωX.other i
    else coordinateOfBits (xBit n ωX i) (yBit n ωY i)

/-- The generated sets are disjoint exactly when the two special-coordinate bits are not both
`true`. -/
theorem disjoint_X_Y_iff (ω : HardSample n) :
    Disjoint (X n ω) (Y n ω) ↔ ¬(ω.xT = true ∧ ω.yT = true) := by
  rw [Set.disjoint_left]
  constructor
  · intro h hbits
    exact h (a := ω.T) (by simpa [X, xBit] using hbits.1) (by simpa [Y, yBit] using hbits.2)
  · intro h i hiX hiY
    by_cases hi : i = ω.T
    · subst hi
      exact h ⟨by simpa [X, xBit] using hiX, by simpa [Y, yBit] using hiY⟩
    · exact not_xBit_and_yBit_of_ne_special n ω hi ⟨hiX, hiY⟩

/-- The generated disjoint coordinate-pair vector. On samples outside `D`, the special coordinate
uses the arbitrary default built into `coordinateOfBits`. -/
def disjointCoordinateVector (ω : HardSample n) : Fin n → DisjointCoordinate :=
  fun i => if i = ω.T then coordinateOfBits ω.xT ω.yT else ω.other i

/-- On disjoint samples, the generated coordinate vector recovers Alice's input bit at every
coordinate. -/
theorem disjointCoordinateVector_xBit_of_mem_disjointEvent
    {ω : HardSample n} (hω : ω ∈ disjointEvent n) (i : Fin n) :
    (disjointCoordinateVector n ω i).xBit = xBit n ω i := by
  have hbits : ¬(ω.xT = true ∧ ω.yT = true) := by
    simpa [disjointEvent, disjoint_X_Y_iff] using hω
  by_cases hi : i = ω.T
  · subst i
    simp [disjointCoordinateVector, coordinateOfBits_xBit hbits, xBit]
  · simp [disjointCoordinateVector, xBit, hi]

/-- On disjoint samples, the generated coordinate vector recovers Bob's input bit at every
coordinate. -/
theorem disjointCoordinateVector_yBit_of_mem_disjointEvent
    {ω : HardSample n} (hω : ω ∈ disjointEvent n) (i : Fin n) :
    (disjointCoordinateVector n ω i).yBit = yBit n ω i := by
  have hbits : ¬(ω.xT = true ∧ ω.yT = true) := by
    simpa [disjointEvent, disjoint_X_Y_iff] using hω
  by_cases hi : i = ω.T
  · subst i
    simp [disjointCoordinateVector, coordinateOfBits_yBit hbits, yBit]
  · simp [disjointCoordinateVector, yBit, hi]

/-- The `other` value at the special coordinate is ignored by the generated input. -/
def ignoredCoordinate (ω : HardSample n) : DisjointCoordinate :=
  ω.other ω.T

/-- Coordinates for the conditioned-on-disjointness sample space: the special coordinate, the
generated disjoint coordinate-pair vector, and the ignored `other` value at the special
coordinate. -/
def disjointModel (ω : HardSample n) :
    Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate :=
  (ω.T, disjointCoordinateVector n ω, ignoredCoordinate n ω)

private def disjointEventEquiv :
    {ω : HardSample n // ω ∈ disjointEvent n} ≃
      Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate where
  toFun ω := disjointModel n ω.1
  invFun p :=
    ⟨{ T := p.1
       xT := (p.2.1 p.1).xBit
       yT := (p.2.1 p.1).yBit
       other := Function.update p.2.1 p.1 p.2.2 },
      by
        change Disjoint
          (X n { T := p.1
                 xT := (p.2.1 p.1).xBit
                 yT := (p.2.1 p.1).yBit
                 other := Function.update p.2.1 p.1 p.2.2 })
          (Y n { T := p.1
                 xT := (p.2.1 p.1).xBit
                 yT := (p.2.1 p.1).yBit
                 other := Function.update p.2.1 p.1 p.2.2 })
        rw [disjoint_X_Y_iff]
        exact DisjointCoordinate.not_xBit_and_yBit (p.2.1 p.1)⟩
  left_inv ω := by
    rcases ω with ⟨⟨T, xT, yT, other⟩, hω⟩
    change Disjoint (X n { T := T, xT := xT, yT := yT, other := other })
      (Y n { T := T, xT := xT, yT := yT, other := other }) at hω
    have hbits : ¬(xT = true ∧ yT = true) := by
      simpa [disjoint_X_Y_iff] using hω
    apply Subtype.ext
    change
      HardSample.mk T
        (disjointCoordinateVector n { T := T, xT := xT, yT := yT, other := other } T).xBit
        (disjointCoordinateVector n { T := T, xT := xT, yT := yT, other := other } T).yBit
        (Function.update
          (disjointCoordinateVector n { T := T, xT := xT, yT := yT, other := other }) T
          (ignoredCoordinate n { T := T, xT := xT, yT := yT, other := other })) =
      HardSample.mk T xT yT other
    congr
    · simpa [disjointCoordinateVector] using coordinateOfBits_xBit hbits
    · simpa [disjointCoordinateVector] using coordinateOfBits_yBit hbits
    · funext i
      by_cases hi : i = T
      · subst i
        simp [ignoredCoordinate]
      · rw [Function.update_of_ne hi]
        simp [disjointCoordinateVector, hi]
  right_inv p := by
    rcases p with ⟨T, coords, junk⟩
    ext i
    · rfl
    · by_cases hi : i = T
      · subst i
        simp [disjointModel, disjointCoordinateVector, coordinateOfBits_xBit_yBit]
      · simp [disjointModel, disjointCoordinateVector, hi]
    · simp [disjointModel, ignoredCoordinate]

noncomputable instance disjointEventFintype :
    Fintype {ω : HardSample n // ω ∈ disjointEvent n} :=
  Fintype.ofEquiv (Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate)
    (disjointEventEquiv n).symm

private def disjointEventInterDisjointModelEquiv
    (z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate) :
    {ω : HardSample n // ω ∈ disjointEvent n ∩ (disjointModel n) ⁻¹' {z}} ≃ Unit where
  toFun _ := Unit.unit
  invFun _ :=
    ⟨((disjointEventEquiv n).symm z).1,
      by
        constructor
        · exact ((disjointEventEquiv n).symm z).2
        · change disjointModel n ((disjointEventEquiv n).symm z).1 = z
          exact (disjointEventEquiv n).right_inv z⟩
  left_inv ω := by
    apply Subtype.ext
    change ((disjointEventEquiv n).symm z).1 = ω.1
    have hmodel : disjointModel n ω.1 = z := by
      simpa using ω.2.2
    have hsub :
        (⟨ω.1, ω.2.1⟩ : {ω : HardSample n // ω ∈ disjointEvent n}) =
          (disjointEventEquiv n).symm z := by
      apply (disjointEventEquiv n).injective
      exact hmodel.trans ((disjointEventEquiv n).right_inv z).symm
    exact (congrArg Subtype.val hsub).symm
  right_inv _ := by
    rfl

noncomputable instance disjointEventInterDisjointModelFintype
    (z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate) :
    Fintype {ω : HardSample n // ω ∈ disjointEvent n ∩ (disjointModel n) ⁻¹' {z}} :=
  Fintype.ofEquiv Unit (disjointEventInterDisjointModelEquiv n z).symm

theorem card_disjointEvent_inter_disjointModel_fiber
    (z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate) :
    Fintype.card {ω : HardSample n // ω ∈ disjointEvent n ∩ (disjointModel n) ⁻¹' {z}} =
      1 := by
  calc
    Fintype.card {ω : HardSample n // ω ∈ disjointEvent n ∩ (disjointModel n) ⁻¹' {z}} =
        Fintype.card Unit :=
      Fintype.card_congr (disjointEventInterDisjointModelEquiv n z)
    _ = 1 := by simp

open Classical in
/-- Under the hard distribution, a singleton fiber of the disjoint model together with `D` has
one ambient sample's worth of mass. -/
theorem measureReal_disjointEvent_inter_disjointModel_fiber
    (z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate) :
    volume.real (disjointEvent n ∩ (disjointModel n) ⁻¹' {z}) =
      (1 / ((n : ℝ) * 4 * 3 ^ (n : ℕ)) : ℝ) := by
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n))
      (disjointEvent n ∩ (disjointModel n) ⁻¹' {z})).toReal =
    (1 / ((n : ℝ) * 4 * 3 ^ (n : ℕ)) : ℝ)
  rw [uniformOn_univ_measureReal_eq_card_subtype,
    card_disjointEvent_inter_disjointModel_fiber, HardSample.card]
  have hn : ((n : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : (3 ^ (n : ℕ) : ℝ) ≠ 0 := by positivity
  norm_num [Nat.cast_mul, Nat.cast_pow]

/-- Dualize the hard sample space by swapping Alice/Bob and reversing coordinate order. -/
def dualHardSample (ω : HardSample n) : HardSample n where
  T := Fin.rev ω.T
  xT := ω.yT
  yT := ω.xT
  other := fun i => DisjointCoordinate.swap (ω.other (Fin.rev i))

/-- Dualizing a hard sample twice recovers the original sample. -/
theorem dualHardSample_dualHardSample (ω : HardSample n) :
    dualHardSample n (dualHardSample n ω) = ω := by
  rcases ω with ⟨T, xT, yT, other⟩
  simp [dualHardSample, DisjointCoordinate.swap_swap]

/-- Alice's bit in the dual hard sample is Bob's original bit at the reversed coordinate. -/
theorem xBit_dualHardSample (ω : HardSample n) (i : Fin n) :
    xBit n (dualHardSample n ω) i = yBit n ω (Fin.rev i) := by
  by_cases hi : i = Fin.rev ω.T
  · subst i
    simp [dualHardSample, xBit, yBit]
  · have hrev : Fin.rev i ≠ ω.T := by
      intro h
      apply hi
      have h' := congrArg Fin.rev h
      simpa using h'
    simp [dualHardSample, xBit, yBit, hi, hrev, DisjointCoordinate.xBit_swap]

/-- Bob's bit in the dual hard sample is Alice's original bit at the reversed coordinate. -/
theorem yBit_dualHardSample (ω : HardSample n) (i : Fin n) :
    yBit n (dualHardSample n ω) i = xBit n ω (Fin.rev i) := by
  have h := xBit_dualHardSample n (dualHardSample n ω) (Fin.rev i)
  simpa [dualHardSample_dualHardSample] using h.symm

/-- Dual hard samples swap Alice's input with Bob's input and reverse coordinates. -/
theorem X_dualHardSample (ω : HardSample n) :
    X n (dualHardSample n ω) = reverseSet n (Y n ω) := by
  ext i
  simp [X, Y, reverseSet, xBit_dualHardSample]

/-- Dual hard samples swap Bob's input with Alice's input and reverse coordinates. -/
theorem Y_dualHardSample (ω : HardSample n) :
    Y n (dualHardSample n ω) = reverseSet n (X n ω) := by
  have h := X_dualHardSample n (dualHardSample n ω)
  have hdual := congrArg (reverseSet n) h
  simpa [dualHardSample_dualHardSample, reverseSet_reverseSet] using hdual.symm

/-- The generated input of a dual hard sample is the reversed, swapped original input. -/
theorem input_dualHardSample (ω : HardSample n) :
    input n (dualHardSample n ω) = (reverseSet n (Y n ω), reverseSet n (X n ω)) := by
  rw [input, X_dualHardSample, Y_dualHardSample]

/-- Hard-sample duality preserves the disjoint-input event. -/
theorem disjointEvent_dualHardSample (ω : HardSample n) :
    dualHardSample n ω ∈ disjointEvent n ↔ ω ∈ disjointEvent n := by
  change Disjoint (X n (dualHardSample n ω)) (Y n (dualHardSample n ω)) ↔
    Disjoint (X n ω) (Y n ω)
  rw [disjoint_X_Y_iff, disjoint_X_Y_iff]
  simp [dualHardSample, and_comm]

/-- Alice's special bit in the dual hard sample is Bob's original special bit. -/
theorem specialX_dualHardSample (ω : HardSample n) :
    specialX n (dualHardSample n ω) = specialY n ω := by
  simp [specialX, specialY, dualHardSample]

/-- Bob's special bit in the dual hard sample is Alice's original special bit. -/
theorem specialY_dualHardSample (ω : HardSample n) :
    specialY n (dualHardSample n ω) = specialX n ω := by
  simp [specialX, specialY, dualHardSample]

/-- The `X_T=Y_T=false` slice is invariant under hard-sample duality. -/
theorem specialZeroZero_dualHardSample (ω : HardSample n) :
    dualHardSample n ω ∈ specialZeroZero n ↔ ω ∈ specialZeroZero n := by
  simp [specialZeroZero, specialBitsEvent, dualHardSample, and_comm]

/-- Alice's full input vector in the dual is Bob's original full vector in reverse order. -/
theorem xVector_dualHardSample (ω : HardSample n) :
    xVector n (dualHardSample n ω) = reverseBoolVector n (yVector n ω) := by
  funext i
  simp [xVector, yVector, reverseBoolVector, xBit_dualHardSample]

/-- Bob's full input vector in the dual is Alice's original full vector in reverse order. -/
theorem yVector_dualHardSample (ω : HardSample n) :
    yVector n (dualHardSample n ω) = reverseBoolVector n (xVector n ω) := by
  funext i
  simp [xVector, yVector, reverseBoolVector, yBit_dualHardSample]

/-- Alice's before-special vector in the dual is Bob's after-special vector in reverse order. -/
theorem xBeforeSpecial_dualHardSample (ω : HardSample n) :
    xBeforeSpecial n (dualHardSample n ω) =
      reverseBoolVector n (yAfterSpecial n ω) := by
  funext i
  change
    (if i < Fin.rev ω.T then xBit n (dualHardSample n ω) i else false) =
      (if ω.T < Fin.rev i then yBit n ω (Fin.rev i) else false)
  rw [xBit_dualHardSample]
  by_cases h : i < Fin.rev ω.T
  · have h' : ω.T < Fin.rev i := (Fin.lt_rev_iff).1 h
    simp [h, h']
  · have h' : ¬ω.T < Fin.rev i := by
      intro h'
      exact h ((Fin.lt_rev_iff).2 h')
    simp [h, h']

/-- Bob's after-special vector in the dual is Alice's before-special vector in reverse order. -/
theorem yAfterSpecial_dualHardSample (ω : HardSample n) :
    yAfterSpecial n (dualHardSample n ω) =
      reverseBoolVector n (xBeforeSpecial n ω) := by
  have h := xBeforeSpecial_dualHardSample n (dualHardSample n ω)
  have hdual := congrArg (reverseBoolVector n) h
  simpa [dualHardSample_dualHardSample,
    reverseBoolVector_reverseBoolVector] using hdual.symm

/-- Alice's `X_≤T` vector in the dual is Bob's `Y_≥T` vector in reverse order. -/
theorem xLeSpecial_dualHardSample (ω : HardSample n) :
    xLeSpecial n (dualHardSample n ω) =
      reverseBoolVector n (yGeSpecial n ω) := by
  funext i
  change
    (if i ≤ Fin.rev ω.T then xBit n (dualHardSample n ω) i else false) =
      (if ω.T ≤ Fin.rev i then yBit n ω (Fin.rev i) else false)
  rw [xBit_dualHardSample]
  by_cases h : i ≤ Fin.rev ω.T
  · have h' : ω.T ≤ Fin.rev i := (Fin.le_rev_iff).1 h
    simp [h, h']
  · have h' : ¬ω.T ≤ Fin.rev i := by
      intro h'
      exact h ((Fin.le_rev_iff).2 h')
    simp [h, h']

/-- Bob's `Y_≥T` vector in the dual is Alice's `X_≤T` vector in reverse order. -/
theorem yGeSpecial_dualHardSample (ω : HardSample n) :
    yGeSpecial n (dualHardSample n ω) =
      reverseBoolVector n (xLeSpecial n ω) := by
  have h := xLeSpecial_dualHardSample n (dualHardSample n ω)
  have hdual := congrArg (reverseBoolVector n) h
  simpa [dualHardSample_dualHardSample,
    reverseBoolVector_reverseBoolVector] using hdual.symm

/-- Alice's corrected conditioning in the dual is Bob's corrected conditioning in recoded form. -/
theorem aliceClaimConditioning_dualHardSample (ω : HardSample n) :
    aliceClaimConditioning n (dualHardSample n ω) =
      dualConditioningValue n (bobClaimConditioning n ω) := by
  rw [aliceClaimConditioning, bobClaimConditioning, dualConditioningValue,
    xBeforeSpecial_dualHardSample, yGeSpecial_dualHardSample]
  simp [specialCoordinate, dualHardSample]

/-- Bob's corrected conditioning in the dual is Alice's corrected conditioning in recoded form. -/
theorem bobClaimConditioning_dualHardSample (ω : HardSample n) :
    bobClaimConditioning n (dualHardSample n ω) =
      dualConditioningValue n (aliceClaimConditioning n ω) := by
  rw [bobClaimConditioning, aliceClaimConditioning, dualConditioningValue,
    xLeSpecial_dualHardSample, yAfterSpecial_dualHardSample]
  simp [specialCoordinate, dualHardSample]

/-- If two samples agree on the data contained in `Z`, then Alice's bit from the first sample and
Bob's bit from the second sample are disjoint away from the special coordinate. -/
theorem not_xBit_left_and_yBit_right_of_same_conditioning
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY)
    {i : Fin n} (hi : i ≠ ωX.T) :
    ¬(xBit n ωX i = true ∧ yBit n ωY i = true) := by
  intro hbits
  by_cases hlt : i < ωX.T
  · have hltY : i < ωY.T := by
      simpa [← hT] using hlt
    have hx_eq : xBit n ωY i = xBit n ωX i := by
      have hfun := congrFun hBefore i
      simpa [xBeforeSpecial, hlt, hltY] using hfun.symm
    exact not_xBit_and_yBit_of_ne_special n ωY (by simpa [← hT] using hi)
      ⟨hx_eq.trans hbits.1, hbits.2⟩
  · have hgt : ωX.T < i := lt_of_le_of_ne (le_of_not_gt hlt) hi.symm
    have hgtY : ωY.T < i := by
      simpa [← hT] using hgt
    have hy_eq : yBit n ωX i = yBit n ωY i := by
      have hfun := congrFun hAfter i
      simpa [yAfterSpecial, hgt, hgtY] using hfun
    exact not_xBit_and_yBit_of_ne_special n ωX hi
      ⟨hbits.1, hy_eq.trans hbits.2⟩

/-- The mixed sample has Alice's input bits from the first sample. -/
theorem xBit_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY)
    (i : Fin n) :
    xBit n (mix n ωX ωY) i = xBit n ωX i := by
  by_cases hi : i = ωX.T
  · subst hi
    simp [mix, xBit]
  · have hdisj :=
      not_xBit_left_and_yBit_right_of_same_conditioning n hT hBefore hAfter hi
    have hdisj' :
        ¬((ωX.other i).xBit = true ∧ yBit n ωY i = true) := by
      simpa [xBit_of_ne_special n ωX hi] using hdisj
    simp [mix, xBit, hi, coordinateOfBits_xBit hdisj']

/-- The mixed sample has Bob's input bits from the second sample. -/
theorem yBit_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY)
    (i : Fin n) :
    yBit n (mix n ωX ωY) i = yBit n ωY i := by
  by_cases hi : i = ωX.T
  · subst hi
    simp [mix, yBit, hT]
  · have hdisj :=
      not_xBit_left_and_yBit_right_of_same_conditioning n hT hBefore hAfter hi
    have hiy : i ≠ ωY.T := by
      simpa [← hT] using hi
    have hdisj' :
        ¬(xBit n ωX i = true ∧ (ωY.other i).yBit = true) := by
      simpa [yBit_of_ne_special n ωY hiy] using hdisj
    simp [mix, yBit, hi, hiy, coordinateOfBits_yBit hdisj']

/-- The mixed sample has Alice's full input from the first sample. -/
theorem X_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    X n (mix n ωX ωY) = X n ωX := by
  ext i
  simp [X, xBit_mix n hT hBefore hAfter i]

/-- The mixed sample has Bob's full input from the second sample. -/
theorem Y_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    Y n (mix n ωX ωY) = Y n ωY := by
  ext i
  simp [Y, yBit_mix n hT hBefore hAfter i]

/-- The mixed sample's generated input is the mixed input pair. -/
theorem input_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    input n (mix n ωX ωY) = (X n ωX, Y n ωY) := by
  rw [input, X_mix n hT hBefore hAfter, Y_mix n hT hBefore hAfter]

/-- Mixing preserves Alice's before-`T` conditioning data from the first sample. -/
theorem xBeforeSpecial_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    xBeforeSpecial n (mix n ωX ωY) = xBeforeSpecial n ωX := by
  funext i
  by_cases hlt : i < ωX.T
  · simpa [xBeforeSpecial, mix, hlt] using xBit_mix n hT hBefore hAfter i
  · simp [xBeforeSpecial, mix, hlt]

/-- Mixing preserves Bob's after-`T` conditioning data from the second sample. -/
theorem yAfterSpecial_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    yAfterSpecial n (mix n ωX ωY) = yAfterSpecial n ωY := by
  funext i
  by_cases hlt : ωY.T < i
  · simpa [yAfterSpecial, mix, hT, hlt] using yBit_mix n hT hBefore hAfter i
  · simp [yAfterSpecial, mix, hT, hlt]

/-- The mixed sample has Alice's special bit from the first sample. -/
theorem specialX_mix (ωX ωY : HardSample n) :
    specialX n (mix n ωX ωY) = specialX n ωX := by
  simp [specialX, mix]

/-- The mixed sample has Bob's special bit from the second sample. -/
theorem specialY_mix (ωX ωY : HardSample n) :
    specialY n (mix n ωX ωY) = specialY n ωY := by
  simp [specialY, mix]

/-- Swapping twice recovers the first sample. This is the involution behind the rectangle-counting
argument for conditional independence on `Z` fibers. -/
theorem mix_mix_swap
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    mix n (mix n ωX ωY) (mix n ωY ωX) = ωX := by
  simp only [mix]
  congr
  funext i
  by_cases hi : i = ωX.T
  · simp [hi]
  · have hx := xBit_mix n hT hBefore hAfter i
    have hy := yBit_mix n hT.symm hBefore.symm hAfter.symm i
    simp only [hi, ↓reduceIte]
    change coordinateOfBits (xBit n (mix n ωX ωY) i) (yBit n (mix n ωY ωX) i) =
      ωX.other i
    rw [hx, hy]
    simp [xBit_of_ne_special n ωX hi, yBit_of_ne_special n ωX hi,
      coordinateOfBits_xBit_yBit]

open Classical in
/-- The hard sample distribution is the product distribution on the independent fields
`T`, `X_T`, `Y_T`, and `other`.  This rectangle form is the most convenient way to compute
probabilities of events depending separately on the four fields. -/
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
  change volume.real sampleEvent = _
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real sampleEvent) = _
  rw [Measure.real, uniformOn_univ_measureReal_eq_card_subtype]
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
  rw [uniformFin_real n TSet, uniformBool_real XSet, uniformBool_real YSet,
    uniformDisjointCoordinateVector_real n OtherSet]
  rw [HardSample.card]
  have hn : (n : ℝ) ≠ 0 := by positivity
  have hpow : (3 ^ (n : ℕ) : ℝ) ≠ 0 := by positivity
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp [hn, hpow]
  ring

open Classical in
/-- The hard distribution creates an intersection with probability `1 / 4`. -/
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
/-- Each prescribed pair of special-coordinate bits has probability `1 / 4`. -/
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
/-- Under the hard distribution, the special coordinate is uniform. -/
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
/-- Under the hard distribution, `T=i` and the special bits intersect with probability
`1/(4n)`. -/
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

/-- The event `(X_T, Y_T) = (0, 0)` has probability `1 / 4`. -/
theorem measureReal_specialZeroZero :
    volume.real (specialZeroZero n) = (1 / 4 : ℝ) := by
  rw [specialZeroZero, measureReal_specialBitsEvent]

/-- The event `Y_T = false` has probability `1 / 2`. -/
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

/-- The disjoint event is the complement of the special-intersection event. -/
theorem disjointEvent_eq_compl_specialIntersect :
    disjointEvent n = (specialIntersect n)ᶜ := by
  ext ω
  simp [disjointEvent, specialIntersect, disjoint_X_Y_iff]

/-- The hard distribution generates disjoint inputs with probability `3 / 4`. -/
theorem measureReal_disjointEvent :
    volume.real (disjointEvent n) = (3 / 4 : ℝ) := by
  rw [disjointEvent_eq_compl_specialIntersect]
  rw [measureReal_compl MeasurableSet.of_discrete]
  rw [measureReal_univ_eq_one]
  rw [show volume.real (specialIntersect n) = (1 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_specialIntersect n]
  norm_num

open Classical in
/-- Under the hard distribution, `T=i` and disjointness have probability `3/(4n)`. -/
theorem measureReal_specialCoordinateEvent_inter_disjointEvent (i : Fin n) :
    volume.real (specialCoordinateEvent n i ∩ disjointEvent n) =
      (3 / (4 * (n : ℝ)) : ℝ) := by
  have hset :
      specialCoordinateEvent n i ∩ disjointEvent n =
        specialCoordinateEvent n i \ (specialCoordinateEvent n i ∩ specialIntersect n) := by
    rw [disjointEvent_eq_compl_specialIntersect]
    ext ω
    simp
  change volume.real (specialCoordinateEvent n i ∩ disjointEvent n) =
    (3 / (4 * (n : ℝ)) : ℝ)
  rw [hset]
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

/-- The disjoint event has positive measure under the hard distribution. -/
theorem measure_disjointEvent_ne_zero :
    volume (disjointEvent n) ≠ 0 := by
  have hreal :
      volume.real (disjointEvent n) ≠ 0 := by
    rw [measureReal_disjointEvent n]
    norm_num
  exact (ENNReal.toReal_ne_zero.mp hreal).1

/-- The hard distribution conditioned on the generated input being disjoint. -/
noncomputable def disjointCondMeasure : Measure (HardSample n) :=
  volume[|disjointEvent n]

open Classical in
/-- Under the disjoint-conditioned hard distribution, the special coordinate remains uniform. -/
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

/-- The special-coordinate singleton event is the corresponding named event. -/
theorem specialCoordinate_preimage_singleton (i : Fin n) :
    (specialCoordinate n) ⁻¹' {i} = specialCoordinateEvent n i := by
  ext ω
  simp [specialCoordinate, specialCoordinateEvent]

open Classical in
/-- Under the disjoint-conditioned distribution, preimages of special-coordinate singletons
have the uniform mass. -/
theorem disjointCondMeasure_measureReal_specialCoordinate_preimage_singleton (i : Fin n) :
    (disjointCondMeasure n).real ((specialCoordinate n) ⁻¹' {i}) =
      (1 / (n : ℝ) : ℝ) := by
  rw [specialCoordinate_preimage_singleton,
    disjointCondMeasure_measureReal_specialCoordinateEvent]

/-- Under the measure conditioned on disjointness, the disjointness event holds almost surely. -/
theorem disjointCondMeasure_ae_disjointEvent :
    ∀ᵐ ω ∂disjointCondMeasure n, ω ∈ disjointEvent n := by
  rw [disjointCondMeasure]
  exact ae_cond_mem MeasurableSet.of_discrete

/-- If Bob's special bit is `false`, the generated inputs are disjoint. -/
theorem mem_disjointEvent_of_specialY_eq_false
    {ω : HardSample n} (hY : specialY n ω = false) :
    ω ∈ disjointEvent n := by
  change Disjoint (X n ω) (Y n ω)
  rw [disjoint_X_Y_iff]
  intro hboth
  rw [show ω.yT = false by simpa [specialY] using hY] at hboth
  simp at hboth

/-- A prescribed special-coordinate bit pair is disjoint exactly when it is not `(true,true)`. -/
theorem specialBitsEvent_subset_disjointEvent
    (bx bY : Bool) (hbits : ¬(bx = true ∧ bY = true)) :
    specialBitsEvent n bx bY ⊆ disjointEvent n := by
  intro ω hω
  rw [specialBitsEvent] at hω
  change Disjoint (X n ω) (Y n ω)
  rw [disjoint_X_Y_iff]
  intro hspecial
  exact hbits ⟨hω.1.symm.trans hspecial.1, hω.2.symm.trans hspecial.2⟩

/-- The `(X_T,Y_T)=(0,0)` slice is contained in the disjoint event. -/
theorem specialZeroZero_subset_disjointEvent :
    specialZeroZero n ⊆ disjointEvent n := by
  intro ω hω
  rw [specialZeroZero, specialBitsEvent] at hω
  exact mem_disjointEvent_of_specialY_eq_false n (by simpa [specialY] using hω.2)

/-- Under the disjoint-conditioned hard distribution, `(X_T,Y_T)=(0,0)` has mass `1 / 3`. -/
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
/-- Under the disjoint-conditioned hard distribution, each non-intersecting special bit-pair has
mass `1/3`. -/
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

/-- Under the disjoint-conditioned hard distribution, `Y_T=false` has mass `2 / 3`. -/
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
/-- The disjoint-conditioned hard distribution, further conditioned on Bob's special bit being
`false`. This is the Alice-side conditioning used in the one-bit Pinsker step. -/
noncomputable def disjointSpecialYFalseMeasure : Measure (HardSample n) :=
  (disjointCondMeasure n)[|(specialY n) ⁻¹' {false}]

open Classical in
/-- Conditioning the disjoint law on `Y_T = false` gives a probability measure. -/
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

/-- Under `D ∧ Y_T=false`, Alice's special bit is uniform. -/
theorem disjointSpecialYFalseMeasure_measureReal_specialX_singleton (b : Bool) :
    (disjointSpecialYFalseMeasure n).real ((specialX n) ⁻¹' {b}) = (1 / 2 : ℝ) := by
  rw [disjointSpecialYFalseMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hden :
      (disjointCondMeasure n).real (((specialY n) ⁻¹' {false}) : Set (HardSample n)) =
        (2 / 3 : ℝ) :=
    disjointCondMeasure_measureReal_specialY_false n
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
/-- Under the disjoint-conditioned distribution, the disjoint model is uniform. -/
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
/-- Under the disjoint-conditioned distribution, the pair of the special coordinate and the
generated disjoint coordinate vector is uniform on `Fin n × {0,1}^n_disj`. -/
theorem disjointCondMeasure_measureReal_specialCoordinate_disjointCoordinateVector_fiber
    (i : Fin n) (coords : Fin n → DisjointCoordinate) :
    (disjointCondMeasure n).real
        (((specialCoordinate n) ⁻¹' {i}) ∩
          ((disjointCoordinateVector n) ⁻¹' {coords})) =
      (1 / (n * 3 ^ (n : ℕ)) : ℝ) := by
  have hpre :=
    FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers
      (Ω := HardSample n)
      (α := Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate)
      (disjointCondMeasure n) (disjointModel n) (fun z => z.1 = i ∧ z.2.1 = coords)
  change (disjointCondMeasure n).real
      {ω | (disjointModel n ω).1 = i ∧ (disjointModel n ω).2.1 = coords} =
    (1 / (n * 3 ^ (n : ℕ)) : ℝ)
  rw [hpre]
  have hfiber (z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate) :
      (disjointCondMeasure n).real ((disjointModel n) ⁻¹' {z}) =
        (1 / (n * 3 ^ (n : ℕ) * 3) : ℝ) := by
    exact disjointCondMeasure_measureReal_disjointModel_fiber n z
  simp_rw [hfiber]
  rw [Finset.sum_ite]
  have hcardFilter :
      (Finset.univ.filter
        (fun z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate =>
          z.1 = i ∧ z.2.1 = coords)).card = 3 := by
    simpa [Fintype.card_subtype] using
      card_disjointModel_fiber_for_specialCoordinate_coordinateVector n i coords
  simp [hcardFilter]

open Classical in
/-- The uniform law on disjoint coordinate vectors is the product of the one-coordinate uniform
laws. -/
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

/-- Under the uniform disjoint-coordinate-vector law, the coordinates are independent. -/
theorem uniformDisjointCoordinateVector_iIndepFun :
    iIndepFun (fun i (coords : Fin n → DisjointCoordinate) => coords i)
      (uniformDisjointCoordinateVector n) := by
  rw [uniformDisjointCoordinateVector_eq_pi]
  exact iIndepFun_pi (fun _ => aemeasurable_id)

/-- Alice's bit at a fixed coordinate of a generated disjoint coordinate vector. -/
def coordinateXBit (i : Fin n) (coords : Fin n → DisjointCoordinate) : Bool :=
  (coords i).xBit

/-- Bob's bit at a fixed coordinate of a generated disjoint coordinate vector. -/
def coordinateYBit (i : Fin n) (coords : Fin n → DisjointCoordinate) : Bool :=
  (coords i).yBit

/-- Alice's input set represented by a generated disjoint coordinate vector. -/
def coordinateXSet (coords : Fin n → DisjointCoordinate) : Set (Fin n) :=
  {i | coordinateXBit n i coords = true}

/-- Bob's input set represented by a generated disjoint coordinate vector. -/
def coordinateYSet (coords : Fin n → DisjointCoordinate) : Set (Fin n) :=
  {i | coordinateYBit n i coords = true}

/-- The input pair represented by a generated disjoint coordinate vector. -/
def coordinateInput (coords : Fin n → DisjointCoordinate) : Set (Fin n) × Set (Fin n) :=
  (coordinateXSet n coords, coordinateYSet n coords)

/-- The protocol transcript as a function of the generated disjoint coordinate vector. -/
noncomputable def coordinateMessage
    (p : ProtocolType n)
    (coords : Fin n → DisjointCoordinate) : TranscriptType n p :=
  p.transcript (coordinateInput n coords)

/-- Alice's coordinate-vector bits before a fixed coordinate, padded by `false` elsewhere. -/
def coordinateXBefore (i : Fin n) (coords : Fin n → DisjointCoordinate) : Fin n → Bool :=
  fun j => if j < i then coordinateXBit n j coords else false

/-- Bob's coordinate-vector bits before a fixed coordinate, padded by `false` elsewhere. -/
def coordinateYBefore (i : Fin n) (coords : Fin n → DisjointCoordinate) : Fin n → Bool :=
  fun j => if j < i then coordinateYBit n j coords else false

/-- Bob's coordinate-vector bits from a fixed coordinate onward, padded by `false` elsewhere. -/
def coordinateYGe (i : Fin n) (coords : Fin n → DisjointCoordinate) : Fin n → Bool :=
  fun j => if i ≤ j then coordinateYBit n j coords else false

/-- The coordinate-vector version of Alice's fixed-coordinate conditioning. -/
def coordinateAliceConditioning (i : Fin n) (coords : Fin n → DisjointCoordinate) :
    (Fin n → Bool) × (Fin n → Bool) :=
  (coordinateXBefore n i coords, coordinateYGe n i coords)

/-- The one-bit-per-coordinate version of Alice's fixed conditioning:
use `X_j` before `i` and `Y_j` from `i` onward. -/
def coordinateAliceCondBit (i k : Fin n) (coords : Fin n → DisjointCoordinate) : Bool :=
  if k < i then coordinateXBit n k coords else coordinateYBit n k coords

/-- Alice's fixed conditioning as one bit from each coordinate. -/
def coordinateAliceCondBits (i : Fin n) (coords : Fin n → DisjointCoordinate) :
    Fin n → Bool :=
  fun k => coordinateAliceCondBit n i k coords

/-- The residual coordinate bit left after conditioning on `coordinateAliceCondBit`. Before `i`
this is Bob's bit; at `i` it is Alice's bit; after `i` it is unused. -/
def coordinateAliceResidualBit (i k : Fin n) (coords : Fin n → DisjointCoordinate) : Bool :=
  if k < i then coordinateYBit n k coords else if k = i then coordinateXBit n k coords else false

/-- Recode the one-bit-per-coordinate Alice conditioning into the padded pair used in the
information term. -/
def coordinateAliceConditioningOfCondBits (i : Fin n) (bits : Fin n → Bool) :
    (Fin n → Bool) × (Fin n → Bool) :=
  (fun j => if j < i then bits j else false,
    fun j => if i ≤ j then bits j else false)

/-- The one-bit-per-coordinate conditioning recodes to the padded-pair conditioning. -/
theorem coordinateAliceConditioning_eq_recode_condBits (i : Fin n) :
    coordinateAliceConditioning n i =
      coordinateAliceConditioningOfCondBits n i ∘ coordinateAliceCondBits n i := by
  funext coords
  ext j
  · by_cases hlt : j < i
    · simp [coordinateAliceConditioning, coordinateXBefore,
        coordinateAliceConditioningOfCondBits, coordinateAliceCondBits,
        coordinateAliceCondBit, hlt]
    · simp [coordinateAliceConditioning, coordinateXBefore,
        coordinateAliceConditioningOfCondBits, hlt]
  · by_cases hge : i ≤ j
    · have hlt : ¬j < i := not_lt_of_ge hge
      simp [coordinateAliceConditioning, coordinateYGe,
        coordinateAliceConditioningOfCondBits, coordinateAliceCondBits,
        coordinateAliceCondBit, hlt, hge]
    · have hlt : j < i := lt_of_not_ge hge
      simp [coordinateAliceConditioning, coordinateYGe,
        coordinateAliceConditioningOfCondBits, coordinateAliceCondBits,
        coordinateAliceCondBit, hlt, hge]

/-- The padded-pair recoding of Alice's one-bit-per-coordinate conditioning is injective. -/
theorem coordinateAliceConditioningOfCondBits_injective (i : Fin n) :
    Function.Injective (coordinateAliceConditioningOfCondBits n i) := by
  intro a b h
  funext j
  have hpair := congrFun (Prod.ext_iff.1 h).1 j
  have hpair' := congrFun (Prod.ext_iff.1 h).2 j
  by_cases hlt : j < i
  · simpa [coordinateAliceConditioningOfCondBits, hlt] using hpair
  · have hge : i ≤ j := le_of_not_gt hlt
    simpa [coordinateAliceConditioningOfCondBits, hge] using hpair'

theorem coordinateAliceCondBits_fiber_eq_iInter (i : Fin n) (bits : Fin n → Bool) :
    (coordinateAliceCondBits n i) ⁻¹' {bits} =
      ⋂ k : Fin n, (coordinateAliceCondBit n i k) ⁻¹' {bits k} := by
  ext coords
  simp [coordinateAliceCondBits, funext_iff]

def coordinateWithCondBit (i k : Fin n) (b : Bool) : DisjointCoordinate :=
  if k < i then
    if b then DisjointCoordinate.leftOnly else DisjointCoordinate.neither
  else
    if b then DisjointCoordinate.rightOnly else DisjointCoordinate.neither

theorem coordinateWithCondBit_spec (i k : Fin n) (b : Bool) :
    (if k < i then (coordinateWithCondBit n i k b).xBit
      else (coordinateWithCondBit n i k b).yBit) = b := by
  by_cases hlt : k < i <;> cases b <;>
    simp [coordinateWithCondBit, hlt, DisjointCoordinate.xBit, DisjointCoordinate.yBit]

open Classical in
/-- Each single-coordinate conditioning bit has positive mass under the uniform disjoint-vector
law. -/
theorem uniformDisjointCoordinateVector_measure_condBit_ne_zero
    (i k : Fin n) (b : Bool) :
    uniformDisjointCoordinateVector n ((coordinateAliceCondBit n i k) ⁻¹' {b}) ≠ 0 := by
  rw [← MeasureTheory.measureReal_ne_zero_iff]
  let coords : Fin n → DisjointCoordinate :=
    Function.update (fun _ => DisjointCoordinate.neither) k (coordinateWithCondBit n i k b)
  have hmem : coords ∈ (coordinateAliceCondBit n i k) ⁻¹' ({b} : Set Bool) := by
    simp [coords, coordinateAliceCondBit, coordinateXBit, coordinateYBit,
      coordinateWithCondBit_spec]
  have hsubset : ({coords} : Set (Fin n → DisjointCoordinate)) ⊆
      (coordinateAliceCondBit n i k) ⁻¹' ({b} : Set Bool) := by
    intro coords' hcoords'
    rw [Set.mem_singleton_iff] at hcoords'
    subst coords'
    exact hmem
  have hsingle_pos :
      0 < (uniformDisjointCoordinateVector n).real ({coords} : Set _) := by
    rw [uniformDisjointCoordinateVector_singleton]
    positivity
  have hle :=
    measureReal_mono (μ := uniformDisjointCoordinateVector n) hsubset
  exact ne_of_gt (hsingle_pos.trans_le hle)

open Classical in
/-- The per-coordinate residual/conditioning pairs are independent under the product-uniform
disjoint-coordinate law. -/
theorem uniformDisjointCoordinateVector_residual_cond_iIndepFun (i : Fin n) :
    iIndepFun
      (fun k (coords : Fin n → DisjointCoordinate) =>
        (coordinateAliceResidualBit n i k coords, coordinateAliceCondBit n i k coords))
      (uniformDisjointCoordinateVector n) := by
  simpa [coordinateAliceResidualBit, coordinateAliceCondBit, coordinateXBit, coordinateYBit]
    using
      (uniformDisjointCoordinateVector_iIndepFun n).comp
        (fun k c =>
          (if k < i then c.yBit else if k = i then c.xBit else false,
            if k < i then c.xBit else c.yBit))
        (fun _ => Measurable.of_discrete)

open Classical in
/-- After fixing Alice's one-bit-per-coordinate conditioning, the current Alice bit is independent
of Bob's earlier bits under the product-uniform disjoint-coordinate law. -/
theorem uniformDisjointCoordinateVector_indep_coordinateXBit_coordinateYBefore_condBits
    (i : Fin n) (bits : Fin n → Bool) :
    IndepFun (coordinateXBit n i) (coordinateYBefore n i)
      ((uniformDisjointCoordinateVector n :
        Measure (Fin n → DisjointCoordinate))[|(coordinateAliceCondBits n i) ⁻¹' {bits}]) := by
  let μ : Measure (Fin n → DisjointCoordinate) :=
    uniformDisjointCoordinateVector n
  rw [coordinateAliceCondBits_fiber_eq_iInter]
  let S : Finset (Fin n) := Finset.univ.filter fun k => k < i
  have hcond_indep :
      iIndepFun (coordinateAliceResidualBit n i)
        (μ[|⋂ k : Fin n, (coordinateAliceCondBit n i k) ⁻¹' ({bits k} : Set Bool)]) := by
    exact ProbabilityTheory.iIndepFun.cond
      (μ := μ)
      (X := coordinateAliceResidualBit n i)
      (Y := coordinateAliceCondBit n i)
      (t := fun k : Fin n => ({bits k} : Set Bool))
      (fun _ => Measurable.of_discrete)
      (by
        simpa [μ] using uniformDisjointCoordinateVector_residual_cond_iIndepFun n i)
      (fun k => by
        simpa [μ] using
          uniformDisjointCoordinateVector_measure_condBit_ne_zero n i k (bits k))
      (fun _ => MeasurableSet.of_discrete)
  have hraw :
      IndepFun
        (fun coords (k : ({i} : Finset (Fin n))) =>
          coordinateAliceResidualBit n i k coords)
        (fun coords (k : S) => coordinateAliceResidualBit n i k coords)
        (μ[|⋂ k : Fin n, (coordinateAliceCondBit n i k) ⁻¹' ({bits k} : Set Bool)]) := by
    refine hcond_indep.indepFun_finset {i} S ?_ (fun _ => Measurable.of_discrete)
    rw [Finset.disjoint_left]
    intro k hk hS
    rw [Finset.mem_singleton] at hk
    subst k
    simp [S] at hS
  let left :
      ((k : ({i} : Finset (Fin n))) → Bool) → Bool :=
    fun f => f ⟨i, by simp⟩
  let right :
      ((k : S) → Bool) → (Fin n → Bool) :=
    fun f j => if hji : j < i then f ⟨j, by simp [S, hji]⟩ else false
  have hcomp : IndepFun (left ∘ fun coords (k : ({i} : Finset (Fin n))) =>
          coordinateAliceResidualBit n i k coords)
        (right ∘ fun coords (k : S) => coordinateAliceResidualBit n i k coords)
        (μ[|⋂ k : Fin n, (coordinateAliceCondBit n i k) ⁻¹' ({bits k} : Set Bool)]) :=
    hraw.comp Measurable.of_discrete Measurable.of_discrete
  have hleft :
      (left ∘ fun coords (k : ({i} : Finset (Fin n))) =>
          coordinateAliceResidualBit n i k coords) = coordinateXBit n i := by
    funext coords
    simp [left, coordinateAliceResidualBit, coordinateXBit]
  have hright :
      (right ∘ fun coords (k : S) => coordinateAliceResidualBit n i k coords) =
        coordinateYBefore n i := by
    funext coords j
    by_cases hji : j < i
    · simp [right, S, coordinateAliceResidualBit, coordinateYBefore, coordinateYBit, hji]
    · simp [right, coordinateYBefore, hji]
  exact IndepFun.congr hcomp (Filter.EventuallyEq.of_eq hleft)
    (Filter.EventuallyEq.of_eq hright)

open Classical in
/-- Product-coordinate form of the fixed-coordinate independence input:
`I(X_i : Y_<i | X_<i,Y_≥i)=0`, first with the one-bit-per-coordinate conditioning. -/
theorem uniformDisjointCoordinateVector_crossInfo_condBits_eq_zero (i : Fin n) :
    I[coordinateXBit n i : coordinateYBefore n i | coordinateAliceCondBits n i ;
      uniformDisjointCoordinateVector n] = 0 := by
  let μ := uniformDisjointCoordinateVector n
  rw [ProbabilityTheory.condMutualInfo_eq_sum'
    (μ := μ) (X := coordinateXBit n i) (Y := coordinateYBefore n i)
    (Z := coordinateAliceCondBits n i) Measurable.of_discrete]
  apply Finset.sum_eq_zero
  intro bits _
  have hindep :=
    uniformDisjointCoordinateVector_indep_coordinateXBit_coordinateYBefore_condBits n i bits
  have hzero :
      I[coordinateXBit n i : coordinateYBefore n i ;
        μ[|(coordinateAliceCondBits n i) ⁻¹' {bits}]] = 0 :=
    hindep.mutualInfo_eq_zero Measurable.of_discrete Measurable.of_discrete
  rw [hzero, mul_zero]

open Classical in
/-- Product-coordinate form of the fixed-coordinate independence input, using the padded-pair
conditioning variable. -/
theorem uniformDisjointCoordinateVector_crossInfo_eq_zero (i : Fin n) :
    I[coordinateXBit n i : coordinateYBefore n i | coordinateAliceConditioning n i ;
      uniformDisjointCoordinateVector n] = 0 := by
  let μ :=
    uniformDisjointCoordinateVector n
  rw [coordinateAliceConditioning_eq_recode_condBits]
  rw [ProbabilityTheory.condMutualInfo_of_inj
    (μ := μ)
    (X := coordinateXBit n i) (Y := coordinateYBefore n i)
    (Z := coordinateAliceCondBits n i)
    Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
    (f := coordinateAliceConditioningOfCondBits n i)
    (coordinateAliceConditioningOfCondBits_injective n i)]
  exact uniformDisjointCoordinateVector_crossInfo_condBits_eq_zero n i

open Classical in
/-- Under `D`, Alice's fixed bit is the corresponding coordinate-vector projection. -/
theorem fixedXBit_ae_eq_coordinateXBit (i : Fin n) :
    fixedXBit n i =ᵐ[disjointCondMeasure n]
      fun ω => coordinateXBit n i (disjointCoordinateVector n ω) := by
  filter_upwards [disjointCondMeasure_ae_disjointEvent n] with ω hω
  exact (disjointCoordinateVector_xBit_of_mem_disjointEvent n hω i).symm

open Classical in
/-- Under `D`, Bob's fixed prefix is the corresponding coordinate-vector projection. -/
theorem fixedYBefore_ae_eq_coordinateYBefore (i : Fin n) :
    fixedYBefore n i =ᵐ[disjointCondMeasure n]
      fun ω => coordinateYBefore n i (disjointCoordinateVector n ω) := by
  filter_upwards [disjointCondMeasure_ae_disjointEvent n] with ω hω
  funext j
  by_cases hji : j < i
  · simp [fixedYBefore, coordinateYBefore, coordinateYBit, hji,
      disjointCoordinateVector_yBit_of_mem_disjointEvent n hω j]
  · simp [fixedYBefore, coordinateYBefore, hji]

open Classical in
/-- Under `D`, Alice's fixed conditioning is the corresponding coordinate-vector projection. -/
theorem fixedAliceConditioning_ae_eq_coordinateAliceConditioning (i : Fin n) :
    fixedAliceConditioning n i =ᵐ[disjointCondMeasure n]
      fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω) := by
  filter_upwards [disjointCondMeasure_ae_disjointEvent n] with ω hω
  ext j <;>
  by_cases hji_lt : j < i <;>
  by_cases hji_ge : i ≤ j <;>
  simp [fixedAliceConditioning, fixedXBefore, fixedYGe, coordinateAliceConditioning,
    coordinateXBefore, coordinateYGe, coordinateXBit, coordinateYBit, hji_lt, hji_ge,
    disjointCoordinateVector_xBit_of_mem_disjointEvent n hω j,
    disjointCoordinateVector_yBit_of_mem_disjointEvent n hω j]

open Classical in
/-- Under `D`, the special coordinate and generated disjoint coordinate vector have the product law:
`T` is uniform and independent of the disjoint coordinate vector. -/
theorem identDistrib_specialCoordinate_disjointCoordinateVector_uniform_prod :
    IdentDistrib
      (fun ω : HardSample n => (specialCoordinate n ω, disjointCoordinateVector n ω))
      id
      (disjointCondMeasure n)
      ((uniformFin n).prod (uniformDisjointCoordinateVector n)) := by
  refine ⟨Measurable.of_discrete.aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id]
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  rintro ⟨i, coords⟩
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real]
  rw [show (fun ω : HardSample n => (specialCoordinate n ω, disjointCoordinateVector n ω)) ⁻¹'
        ({(i, coords)} : Set (Fin n × (Fin n → DisjointCoordinate))) =
      ((specialCoordinate n) ⁻¹' {i}) ∩ ((disjointCoordinateVector n) ⁻¹' {coords}) by
        ext ω
        simp]
  rw [disjointCondMeasure_measureReal_specialCoordinate_disjointCoordinateVector_fiber]
  have hprod :
      ((uniformFin n).prod (uniformDisjointCoordinateVector n)).real
          ({(i, coords)} : Set (Fin n × (Fin n → DisjointCoordinate))) =
        (1 / (n : ℝ)) * (1 / (3 ^ (n : ℕ) : ℝ)) := by
    rw [Measure.real]
    have hsingleton :
        ({(i, coords)} : Set (Fin n × (Fin n → DisjointCoordinate))) =
          ({i} : Set (Fin n)) ×ˢ ({coords} : Set (Fin n → DisjointCoordinate)) := by
      ext z
      simp [Prod.ext_iff]
    rw [hsingleton]
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    rw [← Measure.real, ← Measure.real]
    rw [uniformFin_singleton, uniformDisjointCoordinateVector_singleton]
  rw [hprod]
  have hn : (n : ℝ) ≠ 0 := by positivity
  have hpow : (3 ^ (n : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn, hpow]

open Classical in
/-- The second marginal of the product law for `(T, coordinates)` is the uniform
disjoint-coordinate-vector law. -/
theorem identDistrib_uniformProd_snd_uniformDisjointCoordinateVector :
    IdentDistrib
      Prod.snd
      id
      ((uniformFin n).prod (uniformDisjointCoordinateVector n))
      (uniformDisjointCoordinateVector n) := by
  refine ⟨Measurable.of_discrete.aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id, Measure.map_snd_prod]
  simp

open Classical in
/-- The generated disjoint coordinate vector under `D` has the uniform disjoint-vector law. -/
theorem identDistrib_disjointCoordinateVector_uniform :
    IdentDistrib (disjointCoordinateVector n) id (disjointCondMeasure n)
      (uniformDisjointCoordinateVector n) := by
  have hprod_snd :
      IdentDistrib (disjointCoordinateVector n) Prod.snd (disjointCondMeasure n)
        ((uniformFin n).prod (uniformDisjointCoordinateVector n)) := by
    simpa [Function.comp_def] using
      (identDistrib_specialCoordinate_disjointCoordinateVector_uniform_prod n).comp
        (Measurable.of_discrete
          (f := fun z : Fin n × (Fin n → DisjointCoordinate) => z.2))
  exact hprod_snd.trans (identDistrib_uniformProd_snd_uniformDisjointCoordinateVector n)

open Classical in
/-- Conditioning the product law for `(T, coordinates)` on `T=i` leaves the second coordinate
uniform. -/
theorem identDistrib_uniformProd_snd_uniformDisjointCoordinateVector_cond_fst
    (i : Fin n) :
    IdentDistrib
      Prod.snd
      id
      (((uniformFin n).prod (uniformDisjointCoordinateVector n))[|
        Prod.fst ⁻¹' ({i} : Set (Fin n))])
      (uniformDisjointCoordinateVector n) := by
  let ρ := (uniformFin n).prod (uniformDisjointCoordinateVector n)
  refine ⟨Measurable.of_discrete.aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id]
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro coords
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hden :
      ρ.real (Prod.fst ⁻¹' ({i} : Set (Fin n))) =
        (1 / (n : ℝ) : ℝ) := by
    dsimp [ρ]
    rw [show Prod.fst ⁻¹' ({i} : Set (Fin n)) =
        ({i} : Set (Fin n)) ×ˢ (Set.univ : Set (Fin n → DisjointCoordinate)) by
          ext z
          simp]
    rw [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
    rw [← Measure.real, ← Measure.real]
    rw [uniformFin_singleton, uniformDisjointCoordinateVector_univ]
    ring
  have hnum :
      ρ.real
          (Prod.fst ⁻¹' ({i} : Set (Fin n)) ∩
            Prod.snd ⁻¹' ({coords} : Set (Fin n → DisjointCoordinate))) =
        (1 / ((n : ℝ) * 3 ^ (n : ℕ)) : ℝ) := by
    dsimp [ρ]
    rw [show Prod.fst ⁻¹' ({i} : Set (Fin n)) ∩
          Prod.snd ⁻¹' ({coords} : Set (Fin n → DisjointCoordinate)) =
        ({i} : Set (Fin n)) ×ˢ ({coords} : Set (Fin n → DisjointCoordinate)) by
          ext z
          simp [Prod.ext_iff]]
    rw [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
    rw [← Measure.real, ← Measure.real]
    rw [uniformFin_singleton, uniformDisjointCoordinateVector_singleton]
    ring
  change (ρ.real (Prod.fst ⁻¹' ({i} : Set (Fin n))))⁻¹ *
      ρ.real
        (Prod.fst ⁻¹' ({i} : Set (Fin n)) ∩
          Prod.snd ⁻¹' ({coords} : Set (Fin n → DisjointCoordinate))) =
    (uniformDisjointCoordinateVector n).real {coords}
  rw [hden, hnum, uniformDisjointCoordinateVector_singleton]
  have hn : (n : ℝ) ≠ 0 := by positivity
  have hpow : (3 ^ (n : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn, hpow]

open Classical in
/-- The fixed-coordinate Alice cross-information triple has the same law under `D` as the
corresponding coordinate-vector triple under the uniform disjoint-coordinate law. -/
theorem identDistrib_fixedAliceCrossInfoTriple_uniform (i : Fin n) :
    IdentDistrib
      (fun ω : HardSample n =>
        (fixedXBit n i ω, fixedYBefore n i ω, fixedAliceConditioning n i ω))
      (fun coords : Fin n → DisjointCoordinate =>
        (coordinateXBit n i coords, coordinateYBefore n i coords,
          coordinateAliceConditioning n i coords))
      (disjointCondMeasure n)
      (uniformDisjointCoordinateVector n) := by
  have hfixed_coord :
      (fun ω : HardSample n =>
        (fixedXBit n i ω, fixedYBefore n i ω,
          fixedAliceConditioning n i ω)) =ᵐ[disjointCondMeasure n]
      fun ω : HardSample n =>
        (coordinateXBit n i (disjointCoordinateVector n ω),
          coordinateYBefore n i (disjointCoordinateVector n ω),
          coordinateAliceConditioning n i (disjointCoordinateVector n ω)) := by
    filter_upwards
      [fixedXBit_ae_eq_coordinateXBit n i,
        fixedYBefore_ae_eq_coordinateYBefore n i,
        fixedAliceConditioning_ae_eq_coordinateAliceConditioning n i] with ω hx hy hz
    simp [hx, hy, hz]
  exact
    (IdentDistrib.of_ae_eq Measurable.of_discrete.aemeasurable hfixed_coord).trans
      ((identDistrib_disjointCoordinateVector_uniform n).comp
        (Measurable.of_discrete
          (f := fun coords : Fin n → DisjointCoordinate =>
            (coordinateXBit n i coords, coordinateYBefore n i coords,
              coordinateAliceConditioning n i coords))))

open Classical in
/-- Even after conditioning on `T=i`, the generated disjoint coordinate vector has the uniform
disjoint-vector law. -/
theorem identDistrib_disjointCoordinateVector_uniform_cond_specialCoordinate (i : Fin n) :
    IdentDistrib (disjointCoordinateVector n) id
      ((disjointCondMeasure n)[|specialCoordinate n ← i])
      (uniformDisjointCoordinateVector n) := by
  let ρ : Measure (Fin n × (Fin n → DisjointCoordinate)) :=
    (uniformFin n).prod (uniformDisjointCoordinateVector n)
  have hpair :
      IdentDistrib
        (fun ω : HardSample n => (disjointCoordinateVector n ω, specialCoordinate n ω))
        (fun z : Fin n × (Fin n → DisjointCoordinate) => (z.2, z.1))
        (disjointCondMeasure n)
        ρ := by
    simpa [Function.comp_def, ρ] using
      (identDistrib_specialCoordinate_disjointCoordinateVector_uniform_prod n).comp
        (Measurable.of_discrete
          (f := fun z : Fin n × (Fin n → DisjointCoordinate) => (z.2, z.1)))
  have hcond :
      IdentDistrib
        (disjointCoordinateVector n)
        Prod.snd
        ((disjointCondMeasure n)[|specialCoordinate n ← i])
        (ρ[|Prod.fst ⁻¹' ({i} : Set (Fin n))]) := by
    simpa [ρ] using
      ProbabilityTheory.IdentDistrib.cond_of_pair
        (μ := disjointCondMeasure n) (μ' := ρ)
        (X := disjointCoordinateVector n) (Y := specialCoordinate n)
        (X' := fun z : Fin n × (Fin n → DisjointCoordinate) => z.2)
        (Y' := fun z : Fin n × (Fin n → DisjointCoordinate) => z.1)
        (s := ({i} : Set (Fin n)))
        MeasurableSet.of_discrete Measurable.of_discrete Measurable.of_discrete hpair
  exact hcond.trans
    (by
      simpa [ρ] using
        identDistrib_uniformProd_snd_uniformDisjointCoordinateVector_cond_fst n i)

/-- A measure-preserving self-map leaves every random variable identically distributed with its
pullback along that map. -/
theorem identDistrib_self_comp_measurePreserving
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (F : Ω → α) (hF : Measurable F) :
    IdentDistrib F (F ∘ T) μ μ := by
  refine ⟨hF.aemeasurable, (hF.comp hT.measurable).aemeasurable, ?_⟩
  nth_rw 1 [← hT.map_eq]
  rw [Measure.map_map hF hT.measurable]

/-- The preimage of a singleton under hard-sample duality is the dual singleton. -/
theorem dualHardSample_preimage_singleton (ω : HardSample n) :
    (dualHardSample n) ⁻¹' ({ω} : Set (HardSample n)) =
      {dualHardSample n ω} := by
  ext ω'
  constructor
  · intro h
    have h' : dualHardSample n ω' = ω := by
      simpa using h
    have h'' := congrArg (dualHardSample n) h'
    simpa [dualHardSample_dualHardSample] using h''
  · intro h
    have h' : ω' = dualHardSample n ω := by
      simpa using h
    rw [h']
    simp [dualHardSample_dualHardSample]

/-- The uniform hard-sample measure gives the same mass to a sample and its dual. -/
theorem volume_measureReal_singleton_dualHardSample (ω : HardSample n) :
    volume.real ({dualHardSample n ω} : Set (HardSample n)) =
      volume.real ({ω} : Set (HardSample n)) := by
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real
      ({dualHardSample n ω} : Set (HardSample n))) =
    ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real
      ({ω} : Set (HardSample n)))
  repeat rw [Measure.real]
  rw [uniformOn_univ_measureReal_eq_card_subtype,
    uniformOn_univ_measureReal_eq_card_subtype]
  simp

/-- Hard-sample duality preserves the uniform hard-sample measure. -/
theorem volume_measurePreserving_dualHardSample :
    MeasurePreserving (dualHardSample n)
      volume volume := by
  refine ⟨Measurable.of_discrete, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro ω
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real, dualHardSample_preimage_singleton,
    volume_measureReal_singleton_dualHardSample]

/-- The disjoint-conditioned hard-sample measure gives the same mass to a sample and its dual. -/
theorem disjointCondMeasure_measureReal_singleton_dualHardSample (ω : HardSample n) :
    (disjointCondMeasure n).real ({dualHardSample n ω} : Set (HardSample n)) =
      (disjointCondMeasure n).real ({ω} : Set (HardSample n)) := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  by_cases hω : ω ∈ disjointEvent n
  · have hdual : dualHardSample n ω ∈ disjointEvent n :=
      (disjointEvent_dualHardSample n ω).2 hω
    have hleft :
        disjointEvent n ∩ ({dualHardSample n ω} : Set (HardSample n)) =
          {dualHardSample n ω} := by
      ext η
      simp [hdual]
    have hright : disjointEvent n ∩ ({ω} : Set (HardSample n)) = {ω} := by
      ext η
      simp [hω]
    rw [hleft, hright, volume_measureReal_singleton_dualHardSample]
  · have hdual : dualHardSample n ω ∉ disjointEvent n := by
      intro h
      exact hω ((disjointEvent_dualHardSample n ω).1 h)
    have hleft :
        disjointEvent n ∩ ({dualHardSample n ω} : Set (HardSample n)) =
          ∅ := by
      ext η
      by_cases hη : η = dualHardSample n ω
      · subst η
        simp [hdual]
      · simp [hη]
    have hright : disjointEvent n ∩ ({ω} : Set (HardSample n)) = ∅ := by
      ext η
      by_cases hη : η = ω
      · subst η
        simp [hω]
      · simp [hη]
    rw [hleft, hright]

/-- Hard-sample duality preserves the disjoint-conditioned hard-sample measure. -/
theorem disjointCondMeasure_measurePreserving_dualHardSample :
    MeasurePreserving (dualHardSample n) (disjointCondMeasure n) (disjointCondMeasure n) := by
  refine ⟨Measurable.of_discrete, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro ω
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real, dualHardSample_preimage_singleton,
    disjointCondMeasure_measureReal_singleton_dualHardSample]

/-- Conditioning on a subevent of disjointness is the same under the ambient hard distribution and
under the hard distribution first conditioned on disjointness. -/
theorem volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent
    {A : Set (HardSample n)} (hA : A ⊆ disjointEvent n) :
    volume[|A] = (disjointCondMeasure n)[|A] := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_cond_eq_cond_inter
    MeasurableSet.of_discrete MeasurableSet.of_discrete volume]
  congr 1
  ext ω
  simp [hA]

/-- Conditioning on `(X_T,Y_T)=(0,0)` costs at most a factor `2` relative to conditioning only on
`Y_T=false` under the disjoint distribution. This is the reweighting step before Markov's
inequality. -/
theorem volume_cond_specialZeroZero_measureReal_le_two_mul_disjointSpecialYFalseMeasure
    (S : Set (HardSample n)) :
    (volume[|specialZeroZero n]).real S ≤
      2 * (disjointSpecialYFalseMeasure n).real S := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  have hzero_subset_y0 : specialZeroZero n ⊆ Y0 := by
    intro ω hω
    rw [specialZeroZero, specialBitsEvent] at hω
    simpa [Y0, specialY] using hω.2
  have hcond_zero :
      volume[|specialZeroZero n] = μ[|specialZeroZero n] := by
    simpa [μ] using
      volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent n
        (specialZeroZero_subset_disjointEvent n)
  have hleft :
      (volume[|specialZeroZero n]).real S =
        (μ.real (specialZeroZero n))⁻¹ * μ.real (specialZeroZero n ∩ S) := by
    rw [hcond_zero]
    rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hright :
      (disjointSpecialYFalseMeasure n).real S =
        (μ.real Y0)⁻¹ * μ.real (Y0 ∩ S) := by
    rw [disjointSpecialYFalseMeasure]
    change (μ[|Y0]).real S = (μ.real Y0)⁻¹ * μ.real (Y0 ∩ S)
    rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hzero_mass : μ.real (specialZeroZero n) = (1 / 3 : ℝ) := by
    simpa [μ] using disjointCondMeasure_measureReal_specialZeroZero n
  have hy0_mass : μ.real Y0 = (2 / 3 : ℝ) := by
    simpa [μ, Y0] using disjointCondMeasure_measureReal_specialY_false n
  have hmono : μ.real (specialZeroZero n ∩ S) ≤ μ.real (Y0 ∩ S) :=
    measureReal_mono (by
      intro ω hω
      exact ⟨hzero_subset_y0 hω.1, hω.2⟩)
  rw [hleft, hright, hzero_mass, hy0_mass]
  norm_num
  linarith

/-- The transcript random variable induced by a deterministic protocol on the hard sample space. -/
noncomputable def message
    (p : ProtocolType n)
    (ω : HardSample n) : TranscriptType n p :=
  p.transcript (input n ω)

open Classical in
/-- Under `D`, the transcript is a function of the generated disjoint coordinate vector. -/
theorem message_ae_eq_coordinateMessage
    (p : ProtocolType n) :
    message n p =ᵐ[disjointCondMeasure n]
      fun ω => coordinateMessage n p (disjointCoordinateVector n ω) := by
  filter_upwards [disjointCondMeasure_ae_disjointEvent n] with ω hω
  unfold message coordinateMessage input coordinateInput
  congr
  · ext j
    simp [X, coordinateXSet, coordinateXBit,
      disjointCoordinateVector_xBit_of_mem_disjointEvent n hω j]
  · ext j
    simp [Y, coordinateYSet, coordinateYBit,
      disjointCoordinateVector_yBit_of_mem_disjointEvent n hω j]

/-- The transcript entropy is at most the protocol length in bits, for any ambient measure. -/
theorem entropy_message_le_complexity_mul_log_two_of_measure
    (p : ProtocolType n)
    (μ : Measure (HardSample n)) :
    H[message n p ; μ] ≤
      p.complexity * Real.log 2 := by
  letI : Nonempty (TranscriptType n p) := ⟨p.transcript (∅, ∅)⟩
  exact ProbabilityTheory.entropy_le_nat_mul_log_two_of_card_le_two_pow
    (message n p) μ
    (Deterministic.Protocol.card_transcript_le_two_pow_complexity p)

/-- The dual protocol transcript on the dual hard sample is the original transcript recoded
through protocol duality. -/
theorem message_dualProtocol_dualHardSample
    (p : ProtocolType n)
    (ω : HardSample n) :
    message n (dualProtocol n p) (dualHardSample n ω) =
      dualProtocolTranscriptMap n p (message n p ω) := by
  change (p.swap.comap (reverseSet n) (reverseSet n)).transcript
      (input n (dualHardSample n ω)) =
    dualProtocolTranscriptMap n p (p.transcript (input n ω))
  rw [input_dualHardSample, input]
  rw [← Deterministic.Protocol.transcriptComap_transcript p.swap (reverseSet n) (reverseSet n)
    (reverseSet n (Y n ω)) (reverseSet n (X n ω))]
  rw [reverseSet_reverseSet, reverseSet_reverseSet]
  rw [← Deterministic.Protocol.transcriptSwap_transcript p]
  rfl

/-- Dualize a raw `Z = (M,T,X_<T,Y_>T)` value by recoding the transcript and coarse
conditioning data. -/
def dualRawZValue
    (p : ProtocolType n)
    (z : RawZType n p) :
    RawZType n (dualProtocol n p) :=
  { transcript := dualProtocolTranscriptMap n p z.transcript
    specialCoordinate := Fin.rev z.specialCoordinate
    xBefore := reverseBoolVector n z.yAfter
    yAfter := reverseBoolVector n z.xBefore }

theorem rawZVariable_dualProtocol_dualHardSample
    (p : ProtocolType n)
    (ω : HardSample n) :
    rawZVariable n (dualProtocol n p) (dualHardSample n ω) =
      dualRawZValue n p (rawZVariable n p ω) := by
  apply RawZType.ext
  · exact message_dualProtocol_dualHardSample n p ω
  · simp [rawZVariable, dualRawZValue, specialCoordinate, dualHardSample]
  · simpa [rawZVariable, dualRawZValue] using xBeforeSpecial_dualHardSample n ω
  · simpa [rawZVariable, dualRawZValue] using yAfterSpecial_dualHardSample n ω

/-- Dualize an achievable `Z = (M,T,X_<T,Y_>T)` value by recoding the transcript and coarse
conditioning data. -/
noncomputable def dualZValue
    (p : ProtocolType n)
    (z : ZType n p) :
    ZType n (dualProtocol n p) :=
  ⟨dualRawZValue n p z.raw, by
    rcases z.achievable with ⟨ω, hω⟩
    refine ⟨dualHardSample n ω, ?_⟩
    rw [rawZVariable_dualProtocol_dualHardSample]
    exact congrArg (dualRawZValue n p) hω⟩

/-- Raw `Z` dualization is injective. -/
theorem dualRawZValue_injective
    (p : ProtocolType n) :
    Function.Injective (dualRawZValue n p) := by
  intro z z' h
  apply RawZType.ext
  · exact dualProtocolTranscriptMap_injective n p (congrArg RawZType.transcript h)
  · have hT := congrArg RawZType.specialCoordinate h
    have hT' := congrArg Fin.rev hT
    simpa [dualRawZValue] using hT'
  · exact reverseBoolVector_injective n (congrArg RawZType.yAfter h)
  · exact reverseBoolVector_injective n (congrArg RawZType.xBefore h)

/-- The `Z`-value recoding induced by protocol and hard-sample duality is injective. -/
theorem dualZValue_injective
    (p : ProtocolType n) :
    Function.Injective (dualZValue n p) := by
  intro z z' h
  apply Subtype.ext
  exact dualRawZValue_injective n p (congrArg Subtype.val h)

/-- The `Z` variable for the dual protocol and hard sample is the recoded original `Z`. -/
theorem zVariable_dualProtocol_dualHardSample
    (p : ProtocolType n)
    (ω : HardSample n) :
    zVariable n (dualProtocol n p) (dualHardSample n ω) =
      dualZValue n p (zVariable n p ω) := by
  apply Subtype.ext
  exact rawZVariable_dualProtocol_dualHardSample n p ω

/-- Pulling a recoded dual `Z` fiber back along hard-sample duality gives the original `Z`
fiber. -/
theorem zVariable_dualProtocol_preimage_dualZValue
    (p : ProtocolType n)
    (z : ZType n p) :
    (dualHardSample n) ⁻¹'
        (zFiber n (dualProtocol n p) (dualZValue n p z)) =
      zFiber n p z := by
  ext ω
  change zVariable n (dualProtocol n p) (dualHardSample n ω) = dualZValue n p z ↔
    zVariable n p ω = z
  rw [zVariable_dualProtocol_dualHardSample]
  exact (dualZValue_injective n p).eq_iff

/-- The ambient hard-sample measure gives corresponding original and dual `Z` fibers the same
mass. -/
theorem volume_zVariable_dualProtocol_dualZValue
    (p : ProtocolType n)
    (z : ZType n p) :
    volume
        (zFiber n (dualProtocol n p) (dualZValue n p z)) =
      volume (zFiber n p z) := by
  let μ : Measure (HardSample n) := volume
  let S : Set (HardSample n) :=
    zFiber n (dualProtocol n p) (dualZValue n p z)
  have hpre :
      μ ((dualHardSample n) ⁻¹' S) = μ S :=
    Measure.measure_preimage_of_map_eq_self
      (volume_measurePreserving_dualHardSample n).map_eq
      MeasurableSet.of_discrete.nullMeasurableSet
  rw [← hpre]
  exact congrArg (fun S : Set (HardSample n) => μ S)
    (zVariable_dualProtocol_preimage_dualZValue n p z)

/-- Real-valued version of `volume_zVariable_dualProtocol_dualZValue`. -/
theorem volume_measureReal_zVariable_dualProtocol_dualZValue
    (p : ProtocolType n)
    (z : ZType n p) :
    volume.real
        (zFiber n (dualProtocol n p) (dualZValue n p z)) =
      volume.real (zFiber n p z) := by
  repeat rw [Measure.real]
  rw [volume_zVariable_dualProtocol_dualZValue]

/-- Probabilities under the hard input distribution can be computed on the explicit hard sample
space by taking preimages under `input`. -/
theorem inputDist_measureReal_eq_preimage (S : Set (Set (Fin n) × Set (Fin n))) :
    letI := inputDist n
    volume.real S =
      volume.real ((input n) ⁻¹' S : Set (HardSample n)) := by
  change
    (inputMeasure n).real S =
      volume.real ((input n) ⁻¹' S : Set (HardSample n))
  rw [inputMeasure]
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rfl

/-- The sample-space event where a deterministic protocol errs on disjointness. -/
def protocolErrorEvent
    (p : ProtocolType n) : Set (HardSample n) :=
  {ω | p.run (X n ω) (Y n ω) ≠ disjointness n (X n ω) (Y n ω)}

/-- Distributional error under the hard input distribution is the probability of the named
sample-space error event. -/
theorem distributionalError_inputDist_eq_protocolErrorEvent
    (p : ProtocolType n) :
  p.distributionalError (inputDist n) (disjointness n) =
      volume.real (protocolErrorEvent n p) := by
  rw [Deterministic.Protocol.distributionalError]
  letI := inputDist n
  change volume.real
      {xy : Set (Fin n) × Set (Fin n) | p.run xy.1 xy.2 ≠ disjointness n xy.1 xy.2} =
    volume.real (protocolErrorEvent n p)
  rw [inputDist_measureReal_eq_preimage]
  rfl

/-- The special-coordinate bit-pair. -/
def specialPair (ω : HardSample n) : Bool × Bool :=
  (specialX n ω, specialY n ω)

open Classical in
/-- The law of `X_T` under `D ∧ Y_T=false` is the uniform bit law. -/
theorem disjointSpecialYFalseMeasure_specialX_law_eq_uniformBool :
    Measure.map (specialX n) (disjointSpecialYFalseMeasure n) =
      uniformBool := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  haveI : IsProbabilityMeasure (Measure.map (specialX n) (disjointSpecialYFalseMeasure n)) :=
    Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable (f := specialX n))
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro b
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real]
  rw [disjointSpecialYFalseMeasure_measureReal_specialX_singleton,
    uniformBool_singleton]

/-- The uniform law on one bit has full support. -/
theorem uniformBool_toPMF_ne_zero (b : Bool) :
    uniformBool.toPMF b ≠ 0 := by
  intro hb
  have hreal :
      (uniformBool.toPMF b).toReal =
        (1 / 2 : ℝ) := by
    simpa [Measure.toPMF_apply, Measure.real] using uniformBool_singleton b
  rw [hb] at hreal
  norm_num at hreal

/-- Uniform law on a bit-pair. -/
noncomputable def uniformBoolPair : Measure (Bool × Bool) :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable instance uniformBoolPair_isProbabilityMeasure :
    IsProbabilityMeasure uniformBoolPair := by
  rw [uniformBoolPair]
  infer_instance

/-- Each bit-pair has mass `1 / 4` under the uniform law on two bits. -/
theorem uniformBoolPair_singleton (b : Bool × Bool) :
    uniformBoolPair.real {b} =
      (1 / 4 : ℝ) := by
  rw [uniformBoolPair]
  rw [Measure.real, ProbabilityTheory.uniformOn_univ]
  norm_num [Fintype.card_prod]

/-- The uniform law on two bits is the product of the one-bit uniform laws. -/
theorem uniformBoolPair_eq_prod :
    uniformBoolPair =
      uniformBool.prod uniformBool := by
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro b
  rw [uniformBoolPair_singleton]
  rcases b with ⟨bx, bY⟩
  change (1 / 4 : ℝ) =
    (uniformBool.prod uniformBool ({(bx, bY)})).toReal
  rw [show ({(bx, bY)} : Set (Bool × Bool)) = ({bx} : Set Bool) ×ˢ ({bY} : Set Bool) by
    ext p
    simp [Prod.ext_iff]]
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  have hx :
      (uniformBool ({bx} : Set Bool)).toReal =
        (1 / 2 : ℝ) := by
    simpa [Measure.real] using uniformBool_singleton bx
  have hy :
      (uniformBool ({bY} : Set Bool)).toReal =
        (1 / 2 : ℝ) := by
    simpa [Measure.real] using uniformBool_singleton bY
  rw [hx, hy]
  norm_num

/-- The hard-distribution measure conditioned on a `Z=z` fiber. -/
noncomputable def zFiberMeasure
    (p : ProtocolType n)
    (z : ZType n p) :
    Measure (HardSample n) :=
  volume[|zFiber n p z]

noncomputable instance zFiberMeasure_isProbabilityMeasure
    (p : ProtocolType n)
    (z : ZType n p) :
    IsProbabilityMeasure (zFiberMeasure n p z) := by
  rw [zFiberMeasure]
  exact ProbabilityTheory.cond_isProbabilityMeasure (volume_zFiber_ne_zero n p z)

/-- Conditional probabilities under a `Z=z` fiber are computed by intersecting with the fiber and
dividing by its mass. -/
theorem zFiberMeasure_real_apply
    (p : ProtocolType n)
    (z : ZType n p)
    (S : Set (HardSample n)) :
    (zFiberMeasure n p z).real S =
      (volume.real (zFiber n p z))⁻¹ *
        volume.real ((zFiber n p z) ∩ S) := by
  rw [zFiberMeasure]
  exact ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete _ S

open Classical in
/-- The mass of a `Z` fiber under the Alice-side conditioned measure, with the `3/2` scaling
from `Pr_D[Y_T=false]=2/3` made explicit. -/
theorem disjointSpecialYFalseMeasure_measureReal_zVariable
    (p : ProtocolType n)
    (z : ZType n p) :
    (disjointSpecialYFalseMeasure n).real (zFiber n p z) =
      (3 / 2 : ℝ) *
        (disjointCondMeasure n).real
          (((specialY n) ⁻¹' {false}) ∩ (zFiber n p z)) := by
  rw [disjointSpecialYFalseMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  rw [disjointCondMeasure_measureReal_specialY_false]
  ring

open Classical in
/-- Conditioning first on `Y_T=false` under `D`, then on a `Z` value, is the same as
conditioning under `D` on the intersection of those events. -/
theorem disjointSpecialYFalseMeasure_cond_zVariable_eq_cond_inter
    (p : ProtocolType n)
    (z : ZType n p) :
    (disjointSpecialYFalseMeasure n)[|zVariable n p ← z] =
      (disjointCondMeasure n)[|
        ((specialY n) ⁻¹' {false}) ∩ (zFiber n p z)] := by
  rw [disjointSpecialYFalseMeasure]
  exact ProbabilityTheory.cond_cond_eq_cond_inter
    MeasurableSet.of_discrete MeasurableSet.of_discrete (disjointCondMeasure n)

open Classical in
/-- Conditioning a `Z=z` fiber further on a special Bob-bit value is the same as conditioning the
ambient hard distribution on the intersection of those two fiber events. -/
theorem zFiberMeasure_cond_specialY_eq_volume_cond_inter
    (p : ProtocolType n)
    (z : ZType n p)
    (b : Bool) :
    (zFiberMeasure n p z)[|(specialY n) ⁻¹' {b}] =
      volume[|
        (zFiber n p z) ∩ ((specialY n) ⁻¹' {b})] := by
  rw [zFiberMeasure]
  exact ProbabilityTheory.cond_cond_eq_cond_inter
    MeasurableSet.of_discrete MeasurableSet.of_discrete volume

open Classical in
/-- Conditioning a `Z=z` fiber further on `Y_T=false` agrees with conditioning the
`D ∧ Y_T=false` measure on the same `Z` fiber. -/
theorem zFiberMeasure_cond_specialYFalse_eq_disjointSpecialYFalseMeasure_cond_zVariable
    (p : ProtocolType n)
    (z : ZType n p) :
    (zFiberMeasure n p z)[|(specialY n) ⁻¹' {false}] =
      (disjointSpecialYFalseMeasure n)[|zVariable n p ← z] := by
  rw [zFiberMeasure_cond_specialY_eq_volume_cond_inter]
  rw [show (zFiber n p z) ∩ ((specialY n) ⁻¹' {false}) =
      ((specialY n) ⁻¹' {false}) ∩ (zFiber n p z) by
    ext ω
    simp [and_comm]]
  rw [disjointSpecialYFalseMeasure_cond_zVariable_eq_cond_inter]
  rw [← volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent n
    (by
      intro ω hω
      exact mem_disjointEvent_of_specialY_eq_false n (by simpa using hω.1))]

open Classical in
/-- A positive `Z=z` fiber under `D ∧ Y_T=false` makes the `Y_T=false` branch of the ambient
`Z=z` fiber positive. -/
theorem zFiberMeasure_specialYFalse_ne_zero_of_disjointSpecialYFalseMeasure_ne_zero
    (p : ProtocolType n)
    (z : ZType n p)
    (hz : (disjointSpecialYFalseMeasure n).real (zFiber n p z) ≠ 0) :
    (zFiberMeasure n p z).real ((specialY n) ⁻¹' {false}) ≠ 0 := by
  let Z : Set (HardSample n) := zFiber n p z
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  have hfactor := disjointSpecialYFalseMeasure_measureReal_zVariable n p z
  have hμD_real_ne : (disjointCondMeasure n).real (Y0 ∩ Z) ≠ 0 := by
    intro hzero
    apply hz
    rw [hfactor]
    simp [Y0, Z, hzero]
  have hac_d : disjointCondMeasure n ≪ volume := by
    rw [disjointCondMeasure]
    exact ProbabilityTheory.cond_absolutelyContinuous
  have hμD_ne : (disjointCondMeasure n) (Y0 ∩ Z) ≠ 0 :=
    (MeasureTheory.measureReal_ne_zero_iff
      (μ := disjointCondMeasure n) (s := Y0 ∩ Z)).mp hμD_real_ne
  have hvol_inter_ne : volume (Y0 ∩ Z) ≠ 0 := by
    intro hvol
    exact hμD_ne (hac_d hvol)
  have hvol_inter_real_ne : volume.real (Z ∩ Y0) ≠ 0 := by
    rw [Set.inter_comm]
    exact (MeasureTheory.measureReal_ne_zero_iff
      (μ := volume) (s := Y0 ∩ Z)).mpr hvol_inter_ne
  have hzvol :
      volume Z ≠ 0 :=
    by simpa [Z] using volume_zFiber_ne_zero n p z
  have hzvol_real : volume.real Z ≠ 0 :=
    (MeasureTheory.measureReal_ne_zero_iff
      (μ := volume) (s := Z)).mpr hzvol
  rw [zFiberMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  change
    (volume.real Z)⁻¹ *
      volume.real (Z ∩ Y0) ≠ 0
  exact mul_ne_zero (inv_ne_zero hzvol_real) hvol_inter_real_ne

/-- The conditional law of the special bit-pair on a positive-mass `Z=z` fiber. -/
noncomputable def conditionalSpecialPairLaw
    (p : ProtocolType n)
    (z : ZType n p) : Measure (Bool × Bool) :=
  Measure.map (specialPair n) (zFiberMeasure n p z)

noncomputable instance conditionalSpecialPairLaw_isProbabilityMeasure
    (p : ProtocolType n)
    (z : ZType n p) :
    IsProbabilityMeasure (conditionalSpecialPairLaw n p z) := by
  rw [conditionalSpecialPairLaw]
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable (f := specialPair n))

/-- On a positive-mass `Z=z` fiber, the conditional `specialPair` singleton mass is the
corresponding preimage probability under the fiber measure. -/
theorem conditionalSpecialPairLaw_singleton
    (p : ProtocolType n)
    (z : ZType n p)
    (b : Bool × Bool) :
    Measure.real (conditionalSpecialPairLaw n p z) {b} =
      (zFiberMeasure n p z).real ((specialPair n) ⁻¹' {b}) := by
  rw [conditionalSpecialPairLaw]
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rfl

/-- The conditional law of Alice's special bit on a positive-mass `Z=z` fiber. -/
noncomputable def conditionalSpecialXLaw
    (p : ProtocolType n)
    (z : ZType n p) : Measure Bool :=
  Measure.map (specialX n) (zFiberMeasure n p z)

noncomputable instance conditionalSpecialXLaw_isProbabilityMeasure
    (p : ProtocolType n)
    (z : ZType n p) :
    IsProbabilityMeasure (conditionalSpecialXLaw n p z) := by
  rw [conditionalSpecialXLaw]
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable (f := specialX n))

/-- The conditional law of Bob's special bit on a positive-mass `Z=z` fiber. -/
noncomputable def conditionalSpecialYLaw
    (p : ProtocolType n)
    (z : ZType n p) : Measure Bool :=
  Measure.map (specialY n) (zFiberMeasure n p z)

noncomputable instance conditionalSpecialYLaw_isProbabilityMeasure
    (p : ProtocolType n)
    (z : ZType n p) :
    IsProbabilityMeasure (conditionalSpecialYLaw n p z) := by
  rw [conditionalSpecialYLaw]
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable (f := specialY n))

/-- On a positive-mass `Z=z` fiber, Alice's conditional special-bit singleton mass is the
corresponding preimage probability under the fiber measure. -/
theorem conditionalSpecialXLaw_singleton
    (p : ProtocolType n)
    (z : ZType n p)
    (b : Bool) :
    Measure.real (conditionalSpecialXLaw n p z) {b} =
      (zFiberMeasure n p z).real ((specialX n) ⁻¹' {b}) := by
  rw [conditionalSpecialXLaw]
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rfl

/-- On a positive-mass `Z=z` fiber, Bob's conditional special-bit singleton mass is the
corresponding preimage probability under the fiber measure. -/
theorem conditionalSpecialYLaw_singleton
    (p : ProtocolType n)
    (z : ZType n p)
    (b : Bool) :
    Measure.real (conditionalSpecialYLaw n p z) {b} =
      (zFiberMeasure n p z).real ((specialY n) ⁻¹' {b}) := by
  rw [conditionalSpecialYLaw]
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rfl

/-- The TV distance between the conditional special-pair law on a `Z=z` fiber and the uniform
bit-pair law. -/
noncomputable def zDistance
    (p : ProtocolType n)
    (z : ZType n p) : ℝ :=
  tvDistance (conditionalSpecialPairLaw n p z) uniformBoolPair

/-- The TV distance between Alice's conditional special-bit law and a uniform bit. -/
noncomputable def xDistance
    (p : ProtocolType n)
    (z : ZType n p) : ℝ :=
  tvDistance (conditionalSpecialXLaw n p z) uniformBool

/-- The TV distance between Bob's conditional special-bit law and a uniform bit. -/
noncomputable def yDistance
    (p : ProtocolType n)
    (z : ZType n p) : ℝ :=
  tvDistance (conditionalSpecialYLaw n p z) uniformBool

/-- Alice's one-bit conditional TV distance is nonnegative. -/
theorem xDistance_nonneg
    (p : ProtocolType n)
    (z : ZType n p) :
    0 ≤ xDistance n p z := by
  simp [xDistance, TVDistance.tvDistance_nonneg]

/-- Pulling a dual `Z` fiber intersected with a dual Alice-special-bit event back along
hard-sample duality gives the corresponding original Bob-special-bit event. -/
theorem dualHardSample_preimage_zVariable_dualZValue_inter_specialX
    (p : ProtocolType n)
    (z : ZType n p) (b : Bool) :
    (dualHardSample n) ⁻¹'
        ((zFiber n (dualProtocol n p) (dualZValue n p z)) ∩
          ((specialX n) ⁻¹' {b})) =
      (zFiber n p z) ∩ ((specialY n) ⁻¹' {b}) := by
  ext ω
  change
    zVariable n (dualProtocol n p) (dualHardSample n ω) = dualZValue n p z ∧
        specialX n (dualHardSample n ω) = b ↔
      zVariable n p ω = z ∧ specialY n ω = b
  rw [zVariable_dualProtocol_dualHardSample, specialX_dualHardSample]
  exact and_congr ((dualZValue_injective n p).eq_iff) Iff.rfl

/-- The ambient hard-sample measure gives corresponding original and dual one-bit `Z`-fiber
events the same mass. -/
theorem volume_zVariable_dualProtocol_dualZValue_inter_specialX
    (p : ProtocolType n)
    (z : ZType n p) (b : Bool) :
    volume
        ((zFiber n (dualProtocol n p) (dualZValue n p z)) ∩
          ((specialX n) ⁻¹' {b})) =
      volume
        ((zFiber n p z) ∩ ((specialY n) ⁻¹' {b})) := by
  let μ : Measure (HardSample n) := volume
  let S : Set (HardSample n) :=
    (zFiber n (dualProtocol n p) (dualZValue n p z)) ∩
      ((specialX n) ⁻¹' {b})
  have hpre :
      μ ((dualHardSample n) ⁻¹' S) = μ S :=
    Measure.measure_preimage_of_map_eq_self
      (volume_measurePreserving_dualHardSample n).map_eq
      MeasurableSet.of_discrete.nullMeasurableSet
  rw [← hpre]
  exact congrArg (fun S : Set (HardSample n) => μ S)
    (dualHardSample_preimage_zVariable_dualZValue_inter_specialX n p z b)

/-- Real-valued version of
`volume_zVariable_dualProtocol_dualZValue_inter_specialX`. -/
theorem volume_measureReal_zVariable_dualProtocol_dualZValue_inter_specialX
    (p : ProtocolType n)
    (z : ZType n p) (b : Bool) :
    volume.real
        ((zFiber n (dualProtocol n p) (dualZValue n p z)) ∩
          ((specialX n) ⁻¹' {b})) =
      volume.real
        ((zFiber n p z) ∩ ((specialY n) ⁻¹' {b})) := by
  repeat rw [Measure.real]
  rw [volume_zVariable_dualProtocol_dualZValue_inter_specialX]

open Classical in
/-- The Alice one-bit law on the dual protocol's recoded `Z` fiber is Bob's one-bit law on the
original `Z` fiber. -/
theorem conditionalSpecialXLaw_dualProtocol_dualZValue
    (p : ProtocolType n)
    (z : ZType n p) :
    conditionalSpecialXLaw n (dualProtocol n p) (dualZValue n p z) =
      conditionalSpecialYLaw n p z := by
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro b
  rw [conditionalSpecialXLaw_singleton, conditionalSpecialYLaw_singleton]
  rw [zFiberMeasure_real_apply, zFiberMeasure_real_apply]
  rw [volume_measureReal_zVariable_dualProtocol_dualZValue]
  rw [volume_measureReal_zVariable_dualProtocol_dualZValue_inter_specialX]

open Classical in
/-- The Alice one-bit distance for the dual protocol at the recoded `Z` value is the original
Bob one-bit distance. -/
theorem xDistance_dualProtocol_dualZValue_eq_yDistance
    (p : ProtocolType n)
    (z : ZType n p) :
    xDistance n (dualProtocol n p) (dualZValue n p z) = yDistance n p z := by
  simp [xDistance, yDistance, conditionalSpecialXLaw_dualProtocol_dualZValue n p z]

open Classical in
/-- The dual Alice bad event on the `X_T=Y_T=false` slice is the original Bob bad event. -/
theorem volume_specialZeroZero_inter_xDistance_dualProtocol_eq_yDistance
    (p : ProtocolType n)
    (γ : ℝ) :
    volume.real
        (specialZeroZero n ∩
          {ω | γ < xDistance n (dualProtocol n p) (zVariable n (dualProtocol n p) ω)}) =
      volume.real
        (specialZeroZero n ∩ {ω | γ < yDistance n p (zVariable n p ω)}) := by
  let μ : Measure (HardSample n) := volume
  let Sdual : Set (HardSample n) :=
    specialZeroZero n ∩
      {ω | γ < xDistance n (dualProtocol n p) (zVariable n (dualProtocol n p) ω)}
  let S : Set (HardSample n) :=
    specialZeroZero n ∩ {ω | γ < yDistance n p (zVariable n p ω)}
  have hpre : (dualHardSample n) ⁻¹' Sdual = S := by
    ext ω
    change
      dualHardSample n ω ∈ specialZeroZero n ∧
          γ < xDistance n (dualProtocol n p)
            (zVariable n (dualProtocol n p) (dualHardSample n ω)) ↔
        ω ∈ specialZeroZero n ∧ γ < yDistance n p (zVariable n p ω)
    rw [specialZeroZero_dualHardSample, zVariable_dualProtocol_dualHardSample,
      xDistance_dualProtocol_dualZValue_eq_yDistance]
  have hmeasure : μ S = μ Sdual := by
    have hpre_measure :
        μ ((dualHardSample n) ⁻¹' Sdual) = μ Sdual :=
      Measure.measure_preimage_of_map_eq_self
        (volume_measurePreserving_dualHardSample n).map_eq
        MeasurableSet.of_discrete.nullMeasurableSet
    simpa [hpre] using hpre_measure
  repeat rw [Measure.real]
  rw [hmeasure]

open Classical in
/-- Pinsker for Alice's one-bit fiber distance against the uniform bit. -/
theorem two_mul_xDistance_sq_le_toReal_klDiv_uniformBool
    (p : ProtocolType n)
    (z : ZType n p) :
    2 * xDistance n p z ^ 2 ≤
      (InformationTheory.klDiv
        (conditionalSpecialXLaw n p z)
        uniformBool).toReal := by
  rw [xDistance]
  exact two_mul_tvDistance_sq_le_toReal_klDiv
    (conditionalSpecialXLaw n p z) uniformBool
    (FiniteMeasureSpace.klDiv_ne_top_of_forall_toPMF_ne_zero
      (conditionalSpecialXLaw n p z) uniformBool uniformBool_toPMF_ne_zero)

/-- Alice's one-bit fiber KL cost on a `Z=z` fiber. -/
noncomputable def xFiberKL
    (p : ProtocolType n)
    (z : ZType n p) : ℝ :=
  (InformationTheory.klDiv
    (conditionalSpecialXLaw n p z)
    uniformBool).toReal

/-- Pointwise Pinsker for Alice. -/
theorem two_mul_xDistance_sq_le_xFiberKL
    (p : ProtocolType n)
    (z : ZType n p) :
    2 * xDistance n p z ^ 2 ≤ xFiberKL n p z := by
  simpa [xFiberKL] using two_mul_xDistance_sq_le_toReal_klDiv_uniformBool n p z

open Classical in
/-- Integrated Alice Pinsker bound over the `D ∧ Y_T=false` conditioned measure. -/
theorem two_mul_integral_xDistance_sq_le_integral_xFiberKL_disjointSpecialYFalse
    (p : ProtocolType n) :
    2 * (∫ ω, (xDistance n p (zVariable n p ω)) ^ 2
        ∂(disjointSpecialYFalseMeasure n)) ≤
      ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  have hpoint :
      ∀ ω : HardSample n,
        2 * (xDistance n p (zVariable n p ω)) ^ 2 ≤
          xFiberKL n p (zVariable n p ω) := by
    intro ω
    exact two_mul_xDistance_sq_le_xFiberKL n p (zVariable n p ω)
  have h := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite hpoint
  simpa [μ, integral_const_mul] using h

open Classical in
/-- Jensen's inequality converts a squared Alice-side average-distance estimate under
`D ∧ Y_T=false` into the average-distance estimate used before Markov. -/
theorem disjointSpecialYFalseMeasure_integral_xDistance_le_of_integral_sq_le
    (p : ProtocolType n)
    {γ : ℝ}
    (hsq :
      ∫ ω, (xDistance n p (zVariable n p ω)) ^ 2 ∂(disjointSpecialYFalseMeasure n) ≤
        γ ^ 4) :
    ∫ ω, xDistance n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
      γ ^ 2 := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  let f : HardSample n → ℝ := fun ω => xDistance n p (zVariable n p ω)
  have hjensen :
      (∫ ω, f ω ∂μ) ^ 2 ≤ ∫ ω, (f ω) ^ 2 ∂μ := by
    simpa using
      ConvexOn.map_integral_le
        (by simpa using (show ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) from
          Even.convexOn_pow (𝕜 := ℝ) (by decide : Even 2)))
        (by simpa using
          (show ContinuousOn (fun x : ℝ => x ^ 2) Set.univ from
            (continuous_pow 2).continuousOn))
        isClosed_univ
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
        (Integrable.of_finite (μ := μ))
        (Integrable.of_finite)
  have hsq_bound :
      (∫ ω, f ω ∂μ) ^ 2 ≤ (γ ^ 2) ^ 2 := by
    calc
      (∫ ω, f ω ∂μ) ^ 2
          ≤ ∫ ω, (f ω) ^ 2 ∂μ := hjensen
      _ ≤ γ ^ 4 := by simpa [μ, f] using hsq
      _ = (γ ^ 2) ^ 2 := by ring
  have hint_nonneg :
      0 ≤ ∫ ω, f ω ∂μ :=
    integral_nonneg fun ω => xDistance_nonneg n p (zVariable n p ω)
  have hγ_sq_nonneg : 0 ≤ γ ^ 2 := sq_nonneg γ
  exact (sq_le_sq₀ hint_nonneg hγ_sq_nonneg).mp hsq_bound

open Classical in
/-- Markov's inequality converts the Alice-side average-distance estimate under
`D ∧ Y_T=false` into a bad-`Z` probability bound. -/
theorem disjointSpecialYFalseMeasure_xDistance_bad_le_of_integral_le
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (havg :
      ∫ ω, xDistance n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤ γ ^ 2) :
    (disjointSpecialYFalseMeasure n).real
      {ω | γ < xDistance n p (zVariable n p ω)} ≤ γ := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  let f : HardSample n → ℝ := fun ω => xDistance n p (zVariable n p ω)
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  have hmarkov :
      γ * μ.real {ω : HardSample n | γ ≤ f ω} ≤ ∫ ω, f ω ∂μ :=
    mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := f)
      (ae_of_all _ fun ω => xDistance_nonneg n p (zVariable n p ω))
      Integrable.of_finite γ
  have hbad_le :
      μ.real {ω : HardSample n | γ < f ω} ≤ μ.real {ω : HardSample n | γ ≤ f ω} :=
    measureReal_mono (by
      intro ω hω
      exact le_of_lt (by simpa using hω))
  have hge_le : μ.real {ω : HardSample n | γ ≤ f ω} ≤ γ := by
    have hge_mul :
        μ.real {ω : HardSample n | γ ≤ f ω} * γ ≤ γ ^ 2 := by
      calc
        μ.real {ω : HardSample n | γ ≤ f ω} * γ ≤ ∫ ω, f ω ∂μ := by
          simpa [mul_comm] using hmarkov
        _ ≤ γ ^ 2 := havg
    have hge_nonneg :
        0 ≤ μ.real {ω : HardSample n | γ ≤ f ω} :=
      measureReal_nonneg
    nlinarith
  exact hbad_le.trans hge_le

/-- A `Z` value is good when the conditional special-pair law on its achievable fiber is within
`2γ` of uniform. -/
def goodZ
    (p : ProtocolType n)
    (γ : ℝ)
    (z : ZType n p) : Prop :=
  zDistance n p z ≤ 2 * γ

/-- The good-fiber event, pulled back to the hard sample space through `Z`. -/
def goodZEvent
    (p : ProtocolType n) (γ : ℝ) :
    Set (HardSample n) :=
  {ω | goodZ n p γ (zVariable n p ω)}

/-- The generated input follows the transcript of any deterministic protocol. -/
theorem input_mem_transcript
    (p : ProtocolType n) (ω : HardSample n) :
    input n ω ∈
      Deterministic.Protocol.Transcript.inputSet (message n p ω) :=
  Deterministic.Protocol.mem_transcript p (input n ω)

/-- If a sample has `Z=z`, its generated input follows the transcript component of `z`. -/
theorem input_mem_transcript_of_zVariable_eq
    (p : ProtocolType n)
    {z : ZType n p}
    {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    input n ω ∈ Deterministic.Protocol.Transcript.inputSet z.transcript := by
  have hmsg : message n p ω = z.transcript := by
    simpa [zVariable, rawZVariable, message, ZType.transcript] using
      congrArg (fun z : ZType n p => z.transcript) hω
  simpa [hmsg] using input_mem_transcript n p ω

/-- Equal `Z` value fixes the special coordinate. -/
theorem specialCoordinate_eq_of_zVariable_eq
    (p : ProtocolType n)
    {z : ZType n p}
    {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    specialCoordinate n ω = z.specialCoordinate := by
  simpa [zVariable, rawZVariable, ZType.specialCoordinate] using
    congrArg (fun z : ZType n p => z.specialCoordinate) hω

/-- Equal `Z` value fixes Alice's bits before the special coordinate. -/
theorem xBeforeSpecial_eq_of_zVariable_eq
    (p : ProtocolType n)
    {z : ZType n p}
    {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    xBeforeSpecial n ω = z.xBefore := by
  simpa [zVariable, rawZVariable, ZType.xBefore] using
    congrArg (fun z : ZType n p => z.xBefore) hω

/-- Equal `Z` value fixes Bob's bits after the special coordinate. -/
theorem yAfterSpecial_eq_of_zVariable_eq
    (p : ProtocolType n)
    {z : ZType n p}
    {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    yAfterSpecial n ω = z.yAfter := by
  simpa [zVariable, rawZVariable, ZType.yAfter] using
    congrArg (fun z : ZType n p => z.yAfter) hω

/-- The transcript component of `Z` is a rectangle: two samples in the same `Z` fiber also
contain the two mixed input pairs in that transcript rectangle. -/
theorem mixed_inputs_mem_transcript_of_zVariable_eq
    (p : ProtocolType n)
    {z : ZType n p}
    {ω ω' : HardSample n}
    (hω : zVariable n p ω = z)
    (hω' : zVariable n p ω' = z) :
    (X n ω', Y n ω) ∈ Deterministic.Protocol.Transcript.inputSet z.transcript ∧
      (X n ω, Y n ω') ∈ Deterministic.Protocol.Transcript.inputSet z.transcript := by
  have hrect :
      Rectangle.IsRectangle (Deterministic.Protocol.Transcript.inputSet z.transcript) :=
    Deterministic.Protocol.Transcript.inputSet_isRectangle z.transcript
  have hωmem : (X n ω, Y n ω) ∈ Deterministic.Protocol.Transcript.inputSet z.transcript := by
    simpa [input] using input_mem_transcript_of_zVariable_eq n p hω
  have hω'mem : (X n ω', Y n ω') ∈ Deterministic.Protocol.Transcript.inputSet z.transcript := by
    simpa [input] using input_mem_transcript_of_zVariable_eq n p hω'
  exact (Rectangle.IsRectangle_iff _).mp hrect (X n ω) (X n ω') (Y n ω) (Y n ω')
    hωmem hω'mem

/-- Two samples in the same `Z` fiber have the same special coordinate. -/
theorem specialCoordinate_eq_of_same_zVariable
    (p : ProtocolType n)
    {z : ZType n p}
    {ω ω' : HardSample n}
    (hω : zVariable n p ω = z)
    (hω' : zVariable n p ω' = z) :
    ω.T = ω'.T := by
  have hTω := specialCoordinate_eq_of_zVariable_eq n p hω
  have hTω' := specialCoordinate_eq_of_zVariable_eq n p hω'
  simpa [specialCoordinate] using hTω.trans hTω'.symm

/-- Two samples in the same `Z` fiber have the same `X_<T` conditioning data. -/
theorem xBeforeSpecial_eq_of_same_zVariable
    (p : ProtocolType n)
    {z : ZType n p}
    {ω ω' : HardSample n}
    (hω : zVariable n p ω = z)
    (hω' : zVariable n p ω' = z) :
    xBeforeSpecial n ω = xBeforeSpecial n ω' := by
  have hωx := xBeforeSpecial_eq_of_zVariable_eq n p hω
  have hω'x := xBeforeSpecial_eq_of_zVariable_eq n p hω'
  exact hωx.trans hω'x.symm

/-- Two samples in the same `Z` fiber have the same `Y_>T` conditioning data. -/
theorem yAfterSpecial_eq_of_same_zVariable
    (p : ProtocolType n)
    {z : ZType n p}
    {ω ω' : HardSample n}
    (hω : zVariable n p ω = z)
    (hω' : zVariable n p ω' = z) :
    yAfterSpecial n ω = yAfterSpecial n ω' := by
  have hωy := yAfterSpecial_eq_of_zVariable_eq n p hω
  have hω'y := yAfterSpecial_eq_of_zVariable_eq n p hω'
  exact hωy.trans hω'y.symm

/-- The mixed sample of two samples in the same `Z` fiber remains in that `Z` fiber. -/
theorem zVariable_mix_eq_of_same_zVariable
    (p : ProtocolType n)
    {z : ZType n p}
    {ωX ωY : HardSample n}
    (hωX : zVariable n p ωX = z)
    (hωY : zVariable n p ωY = z) :
    zVariable n p (mix n ωX ωY) = z := by
  have hT := specialCoordinate_eq_of_same_zVariable n p hωX hωY
  have hBefore := xBeforeSpecial_eq_of_same_zVariable n p hωX hωY
  have hAfter := yAfterSpecial_eq_of_same_zVariable n p hωX hωY
  have hinput := input_mix n hT hBefore hAfter
  have hleaf :
      input n (mix n ωX ωY) ∈
        Deterministic.Protocol.Transcript.inputSet z.transcript := by
    have hmixed := mixed_inputs_mem_transcript_of_zVariable_eq n p hωX hωY
    simpa [hinput] using hmixed.2
  have htranscript : p.transcript (input n (mix n ωX ωY)) = z.transcript :=
    Deterministic.Protocol.transcript_eq_of_mem z.transcript hleaf
  have hTz : specialCoordinate n (mix n ωX ωY) = z.specialCoordinate := by
    have hTωX := specialCoordinate_eq_of_zVariable_eq n p hωX
    simpa [specialCoordinate, mix] using hTωX
  have hBeforeZ : xBeforeSpecial n (mix n ωX ωY) = z.xBefore := by
    rw [xBeforeSpecial_mix n hT hBefore hAfter]
    exact xBeforeSpecial_eq_of_zVariable_eq n p hωX
  have hAfterZ : yAfterSpecial n (mix n ωX ωY) = z.yAfter := by
    rw [yAfterSpecial_mix n hT hBefore hAfter]
    exact yAfterSpecial_eq_of_zVariable_eq n p hωY
  apply Subtype.ext
  apply RawZType.ext
  · simpa [zVariable, rawZVariable] using htranscript
  · simpa [zVariable, rawZVariable, ZType.specialCoordinate] using hTz
  · simpa [zVariable, rawZVariable, ZType.xBefore] using hBeforeZ
  · simpa [zVariable, rawZVariable, ZType.yAfter] using hAfterZ

/-- If two samples are in a `Z=z` fiber, and the first has Alice special bit `bX` while the
second has Bob special bit `bY`, then their mix is in the same fiber with special pair
`(bX, bY)`. -/
theorem mix_mem_fiber_inter_specialPair_of_mem_specialX_specialY
    (p : ProtocolType n)
    {z : ZType n p}
    {ωX ωY : HardSample n} {bX bY : Bool}
    (hωX : ωX ∈ (zFiber n p z) ∩ ((specialX n) ⁻¹' {bX}))
    (hωY : ωY ∈ (zFiber n p z) ∩ ((specialY n) ⁻¹' {bY})) :
    mix n ωX ωY ∈ (zFiber n p z) ∩ ((specialPair n) ⁻¹' {(bX, bY)}) := by
  have hZX : zVariable n p ωX = z := by simpa using hωX.1
  have hZY : zVariable n p ωY = z := by simpa using hωY.1
  refine ⟨?_, ?_⟩
  · simpa using zVariable_mix_eq_of_same_zVariable n p hZX hZY
  · have hX : specialX n ωX = bX := by simpa using hωX.2
    have hY : specialY n ωY = bY := by simpa using hωY.2
    simp [specialPair, specialX_mix, specialY_mix, hX, hY]

/-- The swapped mix of two samples in a `Z=z` fiber remains in that fiber. -/
theorem mix_swap_mem_fiber_of_mem_specialX_specialY
    (p : ProtocolType n)
    {z : ZType n p}
    {ωX ωY : HardSample n} {bX bY : Bool}
    (hωX : ωX ∈ (zFiber n p z) ∩ ((specialX n) ⁻¹' {bX}))
    (hωY : ωY ∈ (zFiber n p z) ∩ ((specialY n) ⁻¹' {bY})) :
    mix n ωY ωX ∈ zFiber n p z := by
  have hZX : zVariable n p ωX = z := by simpa using hωX.1
  have hZY : zVariable n p ωY = z := by simpa using hωY.1
  simpa using zVariable_mix_eq_of_same_zVariable n p hZY hZX

/-- If one sample in a fiber has special pair `b` and the other is just in the fiber, mixing with
the special-pair sample on Alice's side lands in the fiber with Alice special bit `b.1`. -/
theorem mix_mem_fiber_inter_specialX_of_mem_specialPair_fiber
    (p : ProtocolType n)
    {z : ZType n p}
    {ωPair ω : HardSample n} {b : Bool × Bool}
    (hωPair : ωPair ∈ (zFiber n p z) ∩ ((specialPair n) ⁻¹' {b}))
    (hω : ω ∈ zFiber n p z) :
    mix n ωPair ω ∈ (zFiber n p z) ∩ ((specialX n) ⁻¹' {b.1}) := by
  have hZPair : zVariable n p ωPair = z := by simpa using hωPair.1
  have hZω : zVariable n p ω = z := by simpa using hω
  have hpair : specialPair n ωPair = b := by simpa using hωPair.2
  refine ⟨?_, ?_⟩
  · simpa using zVariable_mix_eq_of_same_zVariable n p hZPair hZω
  · have hX : specialX n ωPair = b.1 := by
      simpa [specialPair] using congrArg Prod.fst hpair
    simp [specialX_mix, hX]

/-- If one sample in a fiber has special pair `b` and the other is just in the fiber, mixing with
the special-pair sample on Bob's side lands in the fiber with Bob special bit `b.2`. -/
theorem mix_mem_fiber_inter_specialY_of_mem_fiber_specialPair
    (p : ProtocolType n)
    {z : ZType n p}
    {ωPair ω : HardSample n} {b : Bool × Bool}
    (hω : ω ∈ zFiber n p z)
    (hωPair : ωPair ∈ (zFiber n p z) ∩ ((specialPair n) ⁻¹' {b})) :
    mix n ω ωPair ∈ (zFiber n p z) ∩ ((specialY n) ⁻¹' {b.2}) := by
  have hZω : zVariable n p ω = z := by simpa using hω
  have hZPair : zVariable n p ωPair = z := by simpa using hωPair.1
  have hpair : specialPair n ωPair = b := by simpa using hωPair.2
  refine ⟨?_, ?_⟩
  · simpa using zVariable_mix_eq_of_same_zVariable n p hZω hZPair
  · have hY : specialY n ωPair = b.2 := by
      simpa [specialPair] using congrArg Prod.snd hpair
    simp [specialY_mix, hY]

open Classical in
/-- The switching map `(ωX, ωY) ↦ (mix ωX ωY, mix ωY ωX)` gives the cardinal identity
underlying conditional independence of `specialX` and `specialY` on a `Z=z` fiber. -/
theorem card_fiber_inter_specialX_mul_card_fiber_inter_specialY
    (p : ProtocolType n)
    (z : ZType n p)
    (b : Bool × Bool) :
    Fintype.card {ω : HardSample n //
        ω ∈ (zFiber n p z) ∩ ((specialX n) ⁻¹' {b.1})} *
      Fintype.card {ω : HardSample n //
        ω ∈ (zFiber n p z) ∩ ((specialY n) ⁻¹' {b.2})} =
    Fintype.card {ω : HardSample n //
        ω ∈ (zFiber n p z) ∩ ((specialPair n) ⁻¹' {b})} *
      Fintype.card {ω : HardSample n // ω ∈ zFiber n p z} := by
  let A := {ω : HardSample n //
    ω ∈ (zFiber n p z) ∩ ((specialX n) ⁻¹' {b.1})}
  let B := {ω : HardSample n //
    ω ∈ (zFiber n p z) ∩ ((specialY n) ⁻¹' {b.2})}
  let C := {ω : HardSample n //
    ω ∈ (zFiber n p z) ∩ ((specialPair n) ⁻¹' {b})}
  let D := {ω : HardSample n // ω ∈ zFiber n p z}
  have hcard : Fintype.card (A × B) = Fintype.card (C × D) := by
    refine Fintype.card_congr
      { toFun := ?toFun
        invFun := ?invFun
        left_inv := ?left_inv
        right_inv := ?right_inv }
    · intro ab
      refine
        (⟨mix n ab.1.1 ab.2.1,
            mix_mem_fiber_inter_specialPair_of_mem_specialX_specialY n p ab.1.2 ab.2.2⟩,
          ⟨mix n ab.2.1 ab.1.1,
            mix_swap_mem_fiber_of_mem_specialX_specialY n p ab.1.2 ab.2.2⟩)
    · intro cd
      refine
        (⟨mix n cd.1.1 cd.2.1,
            mix_mem_fiber_inter_specialX_of_mem_specialPair_fiber n p cd.1.2 cd.2.2⟩,
          ⟨mix n cd.2.1 cd.1.1,
            mix_mem_fiber_inter_specialY_of_mem_fiber_specialPair n p cd.2.2 cd.1.2⟩)
    · intro ab
      apply Prod.ext
      · apply Subtype.ext
        have hZA : zVariable n p ab.1.1 = z := by simpa using ab.1.2.1
        have hZB : zVariable n p ab.2.1 = z := by simpa using ab.2.2.1
        exact mix_mix_swap n
          (specialCoordinate_eq_of_same_zVariable n p hZA hZB)
          (xBeforeSpecial_eq_of_same_zVariable n p hZA hZB)
          (yAfterSpecial_eq_of_same_zVariable n p hZA hZB)
      · apply Subtype.ext
        have hZA : zVariable n p ab.1.1 = z := by simpa using ab.1.2.1
        have hZB : zVariable n p ab.2.1 = z := by simpa using ab.2.2.1
        exact mix_mix_swap n
          (specialCoordinate_eq_of_same_zVariable n p hZB hZA)
          (xBeforeSpecial_eq_of_same_zVariable n p hZB hZA)
          (yAfterSpecial_eq_of_same_zVariable n p hZB hZA)
    · intro cd
      apply Prod.ext
      · apply Subtype.ext
        have hZC : zVariable n p cd.1.1 = z := by simpa using cd.1.2.1
        have hZD : zVariable n p cd.2.1 = z := cd.2.2
        exact mix_mix_swap n
          (specialCoordinate_eq_of_same_zVariable n p hZC hZD)
          (xBeforeSpecial_eq_of_same_zVariable n p hZC hZD)
          (yAfterSpecial_eq_of_same_zVariable n p hZC hZD)
      · apply Subtype.ext
        have hZC : zVariable n p cd.1.1 = z := by simpa using cd.1.2.1
        have hZD : zVariable n p cd.2.1 = z := cd.2.2
        exact mix_mix_swap n
          (specialCoordinate_eq_of_same_zVariable n p hZD hZC)
          (xBeforeSpecial_eq_of_same_zVariable n p hZD hZC)
          (yAfterSpecial_eq_of_same_zVariable n p hZD hZC)
  simpa [A, B, C, D, Fintype.card_prod] using hcard

open Classical in
/-- Under the uniform hard-distribution measure, real measure is cardinality divided by the size
of the sample space. -/
theorem measureReal_eq_card_subtype_div (S : Set (HardSample n)) :
    volume.real S =
      (Fintype.card {ω : HardSample n // ω ∈ S} : ℝ) /
        Fintype.card (HardSample n) := by
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)) S).toReal = _
  rw [uniformOn_univ_measureReal_eq_card_filter]
  congr 1
  exact_mod_cast (by simp [Fintype.card_subtype])

set_option maxHeartbeats 800000 in
-- The statement contains several dependent subtype cardinalities over protocol leaves; elaborating
-- the local set abbreviations and the final `convert` needs more than the default budget.
open Classical in
/-- The rectangle switching identity, translated from cardinalities to the uniform
hard-distribution measure. -/
theorem fiber_volume_factorization
    (p : ProtocolType n)
    (z : ZType n p)
    (b : Bool × Bool) :
    volume.real (zFiber n p z) *
        volume.real
          ((zFiber n p z) ∩ ((specialPair n) ⁻¹' {b})) =
      volume.real
          ((zFiber n p z) ∩ ((specialX n) ⁻¹' {b.1})) *
        volume.real
          ((zFiber n p z) ∩ ((specialY n) ⁻¹' {b.2})) := by
  let F : Set (HardSample n) := zFiber n p z
  let P : Set (HardSample n) := F ∩ ((specialPair n) ⁻¹' {b})
  let X : Set (HardSample n) := F ∩ ((specialX n) ⁻¹' {b.1})
  let Y : Set (HardSample n) := F ∩ ((specialY n) ⁻¹' {b.2})
  change
    volume.real F * volume.real P =
      volume.real X * volume.real Y
  rw [measureReal_eq_card_subtype_div n F, measureReal_eq_card_subtype_div n P,
    measureReal_eq_card_subtype_div n X, measureReal_eq_card_subtype_div n Y]
  have hcard := card_fiber_inter_specialX_mul_card_fiber_inter_specialY n p z b
  have hcard_real :
      (Fintype.card {ω : HardSample n // ω ∈ X} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ Y} : ℝ) =
      (Fintype.card {ω : HardSample n // ω ∈ P} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ F} : ℝ) := by
    dsimp only [F, P, X, Y]
    exact_mod_cast hcard
  have hN : (Fintype.card (HardSample n) : ℝ) ≠ 0 := by positivity
  have hcard_real' :
      (Fintype.card {ω : HardSample n // ω ∈ F} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ P} : ℝ) =
      (Fintype.card {ω : HardSample n // ω ∈ X} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ Y} : ℝ) := by
    rw [mul_comm, ← hcard_real]
  field_simp [hN]
  convert hcard_real'

/-- To prove the conditional special-pair law factors, it suffices to prove singleton
factorization for the four bit-pairs. -/
theorem conditionalSpecialPairLaw_eq_prod_of_singleton_factorization
    (p : ProtocolType n)
    (z : ZType n p)
    (hfactor : ∀ b : Bool × Bool,
      (conditionalSpecialPairLaw n p z).real {b} =
        (conditionalSpecialXLaw n p z).real {b.1} *
        (conditionalSpecialYLaw n p z).real {b.2}) :
    conditionalSpecialPairLaw n p z =
      (conditionalSpecialXLaw n p z).prod (conditionalSpecialYLaw n p z) := by
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro b
  rw [hfactor b]
  rcases b with ⟨bx, bY⟩
  change
    (conditionalSpecialXLaw n p z).real {bx} *
      (conditionalSpecialYLaw n p z).real {bY} =
      ((conditionalSpecialXLaw n p z).prod
        (conditionalSpecialYLaw n p z) ({(bx, bY)})).toReal
  rw [show ({(bx, bY)} : Set (Bool × Bool)) = ({bx} : Set Bool) ×ˢ ({bY} : Set Bool) by
    ext b
    simp [Prod.ext_iff]]
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  rfl

/-- Singleton factorization can be proved directly on the underlying `Z=z` fiber measure. -/
theorem conditionalSpecialPairLaw_eq_prod_of_zFiberMeasure_factorization
    (p : ProtocolType n)
    (z : ZType n p)
    (hfactor : ∀ b : Bool × Bool,
        (zFiberMeasure n p z).real ((specialPair n) ⁻¹' {b}) =
        (zFiberMeasure n p z).real ((specialX n) ⁻¹' {b.1}) *
        (zFiberMeasure n p z).real ((specialY n) ⁻¹' {b.2})) :
    conditionalSpecialPairLaw n p z =
      (conditionalSpecialXLaw n p z).prod (conditionalSpecialYLaw n p z) := by
  refine conditionalSpecialPairLaw_eq_prod_of_singleton_factorization n p z ?_
  intro b
  rw [conditionalSpecialPairLaw_singleton, conditionalSpecialXLaw_singleton,
    conditionalSpecialYLaw_singleton]
  exact hfactor b

/-- A cross-multiplied version of singleton factorization, phrased using the original hard
distribution instead of conditional fiber probabilities. -/
theorem conditionalSpecialPairLaw_eq_prod_of_fiber_volume_factorization
    (p : ProtocolType n)
    (z : ZType n p)
    (hfactor : ∀ b : Bool × Bool,
      volume.real (zFiber n p z) *
          volume.real
            ((zFiber n p z) ∩ ((specialPair n) ⁻¹' {b})) =
        volume.real
            ((zFiber n p z) ∩ ((specialX n) ⁻¹' {b.1})) *
          volume.real
            ((zFiber n p z) ∩ ((specialY n) ⁻¹' {b.2}))) :
    conditionalSpecialPairLaw n p z =
      (conditionalSpecialXLaw n p z).prod (conditionalSpecialYLaw n p z) := by
  refine conditionalSpecialPairLaw_eq_prod_of_zFiberMeasure_factorization n p z ?_
  intro b
  rw [zFiberMeasure_real_apply, zFiberMeasure_real_apply, zFiberMeasure_real_apply]
  have hm :
      volume.real (zFiber n p z) ≠ 0 := by
    exact (MeasureTheory.measureReal_ne_zero_iff
      (μ := volume) (s := zFiber n p z)).mpr (volume_zFiber_ne_zero n p z)
  have h := hfactor b
  field_simp [hm]
  exact h

open Classical in
/-- The protocol transcript is a rectangle on each coarse fiber, so conditioned on a positive
`Z=z` fiber the special bits factor as the product of their two marginals. -/
theorem conditionalSpecialPairLaw_eq_prod
    (p : ProtocolType n)
    (z : ZType n p) :
    conditionalSpecialPairLaw n p z =
      (conditionalSpecialXLaw n p z).prod (conditionalSpecialYLaw n p z) := by
  exact conditionalSpecialPairLaw_eq_prod_of_fiber_volume_factorization n p z
    (fiber_volume_factorization n p z)

open Classical in
/-- A product special-pair law gives singleton factorization of the conditional bit laws on the
same `Z` fiber. -/
theorem conditionalSpecialPairLaw_singleton_factorization_of_eq_prod
    (p : ProtocolType n)
    (z : ZType n p)
    (hprod :
      conditionalSpecialPairLaw n p z =
        (conditionalSpecialXLaw n p z).prod (conditionalSpecialYLaw n p z))
    (b : Bool × Bool) :
    (conditionalSpecialPairLaw n p z).real {b} =
      (conditionalSpecialXLaw n p z).real {b.1} *
        (conditionalSpecialYLaw n p z).real {b.2} := by
  rw [hprod]
  rcases b with ⟨bX, bY⟩
  change
    ((conditionalSpecialXLaw n p z).prod
      (conditionalSpecialYLaw n p z) ({(bX, bY)})).toReal =
      (conditionalSpecialXLaw n p z).real {bX} *
        (conditionalSpecialYLaw n p z).real {bY}
  rw [show ({(bX, bY)} : Set (Bool × Bool)) = ({bX} : Set Bool) ×ˢ ({bY} : Set Bool) by
    ext b
    simp [Prod.ext_iff]]
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  rfl

open Classical in
/-- On a product-law `Z` fiber, conditioning on one Bob special-bit value does not change Alice's
special-bit law. -/
theorem conditionalSpecialXLaw_eq_cond_specialY_of_prod
    (p : ProtocolType n)
    (z : ZType n p)
    (hprod :
      conditionalSpecialPairLaw n p z =
        (conditionalSpecialXLaw n p z).prod (conditionalSpecialYLaw n p z))
    (bY : Bool)
    (hY : (zFiberMeasure n p z).real ((specialY n) ⁻¹' {bY}) ≠ 0) :
    conditionalSpecialXLaw n p z =
      Measure.map (specialX n) ((zFiberMeasure n p z)[|(specialY n) ⁻¹' {bY}]) := by
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro bX
  rw [conditionalSpecialXLaw_singleton]
  rw [Measure.real]
  change ((zFiberMeasure n p z) ((specialX n) ⁻¹' {bX})).toReal =
    (Measure.map (specialX n) ((zFiberMeasure n p z)[|(specialY n) ⁻¹' {bY}]) {bX}).toReal
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real]
  change (zFiberMeasure n p z).real ((specialX n) ⁻¹' {bX}) =
    ((zFiberMeasure n p z)[|(specialY n) ⁻¹' {bY}]).real ((specialX n) ⁻¹' {bX})
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hpair :
      ((specialY n) ⁻¹' {bY}) ∩ ((specialX n) ⁻¹' {bX}) =
        (specialPair n) ⁻¹' {(bX, bY)} := by
    ext ω
    simp [specialPair, specialX, specialY, and_comm]
  have hfactor :=
    conditionalSpecialPairLaw_singleton_factorization_of_eq_prod n p z hprod (bX, bY)
  rw [conditionalSpecialPairLaw_singleton, conditionalSpecialXLaw_singleton,
    conditionalSpecialYLaw_singleton] at hfactor
  rw [hpair, hfactor]
  field_simp [hY]

open Classical in
/-- Rectangle switching implies the fiber identity
`p(X_T | Z=z) = p(X_T | Z=z, Y_T=false)`. -/
theorem conditionalSpecialXLaw_eq_cond_specialYFalse
    (p : ProtocolType n)
    (z : ZType n p)
    (hY : (zFiberMeasure n p z).real ((specialY n) ⁻¹' {false}) ≠ 0) :
    conditionalSpecialXLaw n p z =
      Measure.map (specialX n) ((zFiberMeasure n p z)[|(specialY n) ⁻¹' {false}]) :=
  conditionalSpecialXLaw_eq_cond_specialY_of_prod n p z
    (conditionalSpecialPairLaw_eq_prod n p z) false hY

open Classical in
/-- After rectangle switching, Alice's `xFiberKL` can be computed by first conditioning on
`Y_T=false` inside the `Z=z` fiber. -/
theorem xFiberKL_eq_cond_specialYFalse_klDiv
    (p : ProtocolType n)
    (z : ZType n p)
    (hY : (zFiberMeasure n p z).real ((specialY n) ⁻¹' {false}) ≠ 0) :
    xFiberKL n p z =
      (InformationTheory.klDiv
        (Measure.map (specialX n) ((zFiberMeasure n p z)[|(specialY n) ⁻¹' {false}]))
        uniformBool).toReal := by
  rw [xFiberKL]
  rw [conditionalSpecialXLaw_eq_cond_specialYFalse n p z hY]

open Classical in
/-- Alice's `xFiberKL` can be rewritten as KL for the special Alice bit under
`D ∧ Y_T=false` conditioned on the same `Z=z` fiber. -/
theorem xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv
    (p : ProtocolType n)
    (z : ZType n p)
    (hY : (zFiberMeasure n p z).real ((specialY n) ⁻¹' {false}) ≠ 0) :
    xFiberKL n p z =
      (InformationTheory.klDiv
        (Measure.map (specialX n)
          ((disjointSpecialYFalseMeasure n)[|zVariable n p ← z]))
        uniformBool).toReal := by
  rw [xFiberKL_eq_cond_specialYFalse_klDiv n p z hY]
  rw [zFiberMeasure_cond_specialYFalse_eq_disjointSpecialYFalseMeasure_cond_zVariable]

open Classical in
/-- Positive mass under `D ∧ Y_T=false` supplies the positivity hypotheses needed to rewrite
Alice's fiber KL using the `D ∧ Y_T=false, Z=z` conditional law. -/
theorem xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv_of_ne_zero
    (p : ProtocolType n)
    (z : ZType n p)
    (hz : (disjointSpecialYFalseMeasure n).real (zFiber n p z) ≠ 0) :
    xFiberKL n p z =
      (InformationTheory.klDiv
        (Measure.map (specialX n)
          ((disjointSpecialYFalseMeasure n)[|zVariable n p ← z]))
        uniformBool).toReal := by
  exact xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv n p z
    (zFiberMeasure_specialYFalse_ne_zero_of_disjointSpecialYFalseMeasure_ne_zero n p z hz)

open Classical in
/-- Product-distribution step for `Z` fibers. Conditioned on a transcript rectangle and the
coarse data, the special bits are independent, so the pair TV distance is controlled by the two
one-bit TV distances. -/
theorem zDistance_le_xDistance_add_yDistance
    (p : ProtocolType n)
    (z : ZType n p) :
    zDistance n p z ≤ xDistance n p z + yDistance n p z := by
  simpa [zDistance, xDistance, yDistance, conditionalSpecialPairLaw_eq_prod n p z,
    uniformBoolPair_eq_prod] using
    TVDistance.tvDistance_prod_le
      (conditionalSpecialXLaw n p z) uniformBool
      (conditionalSpecialYLaw n p z) uniformBool

/-- If both one-bit marginal distances on a `Z` fiber are at most `γ`, then the fiber is good. -/
theorem mem_goodZEvent_of_xDistance_yDistance_le
    (p : ProtocolType n)
    {γ : ℝ} {ω : HardSample n}
    (hx : xDistance n p (zVariable n p ω) ≤ γ)
    (hy : yDistance n p (zVariable n p ω) ≤ γ) :
    ω ∈ goodZEvent n p γ := by
  have h := zDistance_le_xDistance_add_yDistance n p (zVariable n p ω)
  change zDistance n p (zVariable n p ω) ≤ 2 * γ
  linarith

/-- The corrected Alice special-coordinate information term:
`I(X_T : M | T, X_<T, Y_≥T, D)`. -/
noncomputable def aliceInfoTerm
    (p : ProtocolType n) : ℝ :=
  I[specialX n : message n p | aliceClaimConditioning n ; disjointCondMeasure n]

/-- The corrected Bob special-coordinate information term:
`I(Y_T : M | T, X_≤T, Y_>T, D)`. -/
noncomputable def bobInfoTerm
    (p : ProtocolType n) : ℝ :=
  I[specialY n : message n p | bobClaimConditioning n ; disjointCondMeasure n]

/-- The total corrected special-coordinate information. -/
noncomputable def claimInfo
    (p : ProtocolType n) : ℝ :=
  aliceInfoTerm n p + bobInfoTerm n p

open Classical in
/-- Bob's corrected information term is nonnegative. -/
theorem bobInfoTerm_nonneg
    (p : ProtocolType n) :
    0 ≤ bobInfoTerm n p := by
  rw [bobInfoTerm]
  exact ProbabilityTheory.condMutualInfo_nonneg
    (μ := disjointCondMeasure n)
    (X := specialY n) (Y := message n p) (Z := bobClaimConditioning n)
    Measurable.of_discrete Measurable.of_discrete

/-- Alice's information term is bounded by the total corrected information. -/
theorem aliceInfoTerm_le_claimInfo
    (p : ProtocolType n) :
    aliceInfoTerm n p ≤ claimInfo n p := by
  rw [claimInfo]
  linarith [bobInfoTerm_nonneg n p]

open Classical in
/-- Alice's corrected information term for the dual protocol is Bob's corrected information term
for the original protocol. -/
theorem aliceInfoTerm_dualProtocol_eq_bobInfoTerm
    (p : ProtocolType n) :
    aliceInfoTerm n (dualProtocol n p) = bobInfoTerm n p := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  have hmap : MeasurePreserving (dualHardSample n) μ μ := by
    simpa [μ] using disjointCondMeasure_measurePreserving_dualHardSample n
  have hpull :
      aliceInfoTerm n (dualProtocol n p) =
        I[fun ω => specialX n (dualHardSample n ω) :
          fun ω => message n (dualProtocol n p) (dualHardSample n ω) |
          fun ω => aliceClaimConditioning n (dualHardSample n ω) ; μ] := by
    rw [aliceInfoTerm]
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite
      (μ := μ) (μ' := μ)
      (X := specialX n) (Y := message n (dualProtocol n p))
      (Z := aliceClaimConditioning n)
      (X' := fun ω => specialX n (dualHardSample n ω))
      (Y' := fun ω => message n (dualProtocol n p) (dualHardSample n ω))
      (Z' := fun ω => aliceClaimConditioning n (dualHardSample n ω))
      (identDistrib_self_comp_measurePreserving hmap
        (fun ω =>
          (specialX n ω, message n (dualProtocol n p) ω, aliceClaimConditioning n ω))
        Measurable.of_discrete)
  rw [hpull]
  have hrec :
      I[specialY n :
          (fun ω => dualProtocolTranscriptMap n p (message n p ω)) |
          (fun ω => dualConditioningValue n (bobClaimConditioning n ω)) ; μ] =
        I[specialY n : message n p | bobClaimConditioning n ; μ] := by
    simpa [Function.comp_def] using
      ProbabilityTheory.condMutualInfo_comp_right_conditioning_of_injective
        (μ := μ) (X := specialY n) (Y := message n p) (Z := bobClaimConditioning n)
        (f := dualProtocolTranscriptMap n p) (g := dualConditioningValue n)
        Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
        Measurable.of_discrete Measurable.of_discrete
        (dualProtocolTranscriptMap_injective n p) (dualConditioningValue_injective n)
  simpa [μ, bobInfoTerm, specialX_dualHardSample, message_dualProtocol_dualHardSample,
    aliceClaimConditioning_dualHardSample] using hrec

open Classical in
/-- Bob's corrected information term for the dual protocol is Alice's corrected information term
for the original protocol. -/
theorem bobInfoTerm_dualProtocol_eq_aliceInfoTerm
    (p : ProtocolType n) :
    bobInfoTerm n (dualProtocol n p) = aliceInfoTerm n p := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  have hmap : MeasurePreserving (dualHardSample n) μ μ := by
    simpa [μ] using disjointCondMeasure_measurePreserving_dualHardSample n
  have hpull :
      bobInfoTerm n (dualProtocol n p) =
        I[fun ω => specialY n (dualHardSample n ω) :
          fun ω => message n (dualProtocol n p) (dualHardSample n ω) |
          fun ω => bobClaimConditioning n (dualHardSample n ω) ; μ] := by
    rw [bobInfoTerm]
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite
      (μ := μ) (μ' := μ)
      (X := specialY n) (Y := message n (dualProtocol n p))
      (Z := bobClaimConditioning n)
      (X' := fun ω => specialY n (dualHardSample n ω))
      (Y' := fun ω => message n (dualProtocol n p) (dualHardSample n ω))
      (Z' := fun ω => bobClaimConditioning n (dualHardSample n ω))
      (identDistrib_self_comp_measurePreserving hmap
        (fun ω =>
          (specialY n ω, message n (dualProtocol n p) ω, bobClaimConditioning n ω))
        Measurable.of_discrete)
  rw [hpull]
  have hrec :
      I[specialX n :
          (fun ω => dualProtocolTranscriptMap n p (message n p ω)) |
          (fun ω => dualConditioningValue n (aliceClaimConditioning n ω)) ; μ] =
        I[specialX n : message n p | aliceClaimConditioning n ; μ] := by
    simpa [Function.comp_def] using
      ProbabilityTheory.condMutualInfo_comp_right_conditioning_of_injective
        (μ := μ) (X := specialX n) (Y := message n p) (Z := aliceClaimConditioning n)
        (f := dualProtocolTranscriptMap n p) (g := dualConditioningValue n)
        Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
        Measurable.of_discrete Measurable.of_discrete
        (dualProtocolTranscriptMap_injective n p) (dualConditioningValue_injective n)
  simpa [μ, aliceInfoTerm, specialY_dualHardSample, message_dualProtocol_dualHardSample,
    bobClaimConditioning_dualHardSample] using hrec

open Classical in
/-- Full-vector information for the dual protocol is the swapped full-vector information for the
original protocol. -/
theorem xVector_message_info_dualProtocol_eq_yVector_message_info
    (p : ProtocolType n) :
    I[xVector n : message n (dualProtocol n p) | yVector n ; disjointCondMeasure n] =
      I[yVector n : message n p | xVector n ; disjointCondMeasure n] := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  have hmap : MeasurePreserving (dualHardSample n) μ μ := by
    simpa [μ] using disjointCondMeasure_measurePreserving_dualHardSample n
  have hpull :
      I[xVector n : message n (dualProtocol n p) | yVector n ; μ] =
        I[fun ω => xVector n (dualHardSample n ω) :
          fun ω => message n (dualProtocol n p) (dualHardSample n ω) |
          fun ω => yVector n (dualHardSample n ω) ; μ] := by
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite
      (μ := μ) (μ' := μ)
      (X := xVector n) (Y := message n (dualProtocol n p)) (Z := yVector n)
      (X' := fun ω => xVector n (dualHardSample n ω))
      (Y' := fun ω => message n (dualProtocol n p) (dualHardSample n ω))
      (Z' := fun ω => yVector n (dualHardSample n ω))
      (identDistrib_self_comp_measurePreserving hmap
        (fun ω => (xVector n ω, message n (dualProtocol n p) ω, yVector n ω))
        Measurable.of_discrete)
  rw [show disjointCondMeasure n = μ by rfl, hpull]
  have hrec :
      I[(fun ω => reverseBoolVector n (yVector n ω)) :
          (fun ω => dualProtocolTranscriptMap n p (message n p ω)) |
          (fun ω => reverseBoolVector n (xVector n ω)) ; μ] =
        I[yVector n : message n p | xVector n ; μ] := by
    simpa [Function.comp_def] using
      ProbabilityTheory.condMutualInfo_of_inj'
        (X := yVector n) (Y := message n p) (Z := xVector n)
        Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete μ
        (reverseBoolVector_injective n) (dualProtocolTranscriptMap_injective n p)
        (reverseBoolVector_injective n)
  simpa [μ, xVector_dualHardSample, yVector_dualHardSample,
    message_dualProtocol_dualHardSample] using hrec

open Classical in
/-- The total corrected information is invariant under protocol duality. -/
theorem claimInfo_dualProtocol
    (p : ProtocolType n) :
    claimInfo n (dualProtocol n p) = claimInfo n p := by
  rw [claimInfo, aliceInfoTerm_dualProtocol_eq_bobInfoTerm,
    bobInfoTerm_dualProtocol_eq_aliceInfoTerm, claimInfo, add_comm]

open Classical in
/-- The fixed-coordinate summand `I(X_i : M | X_<i, Y_≥i)`. -/
noncomputable def fixedAliceInfoTerm
    (p : ProtocolType n)
    (i : Fin n) : ℝ :=
  I[fixedXBit n i : message n p | fixedAliceConditioning n i ; disjointCondMeasure n]

open Classical in
/-- The fixed-coordinate term with the full `Y` vector in the conditioning. -/
noncomputable def fixedAliceFullYInfoTerm
    (p : ProtocolType n)
    (i : Fin n) : ℝ :=
  I[fixedXBit n i : message n p | fixedAliceFullYConditioning n i ; disjointCondMeasure n]

open Classical in
/-- The zero cross-information term `I(X_i : Y_<i | X_<i, Y_≥i)`. -/
noncomputable def fixedAliceCrossInfoTerm (i : Fin n) : ℝ :=
  I[fixedXBit n i : fixedYBefore n i | fixedAliceConditioning n i ; disjointCondMeasure n]

open Classical in
/-- Fixed-coordinate independence input for the hard distribution conditioned on `D`:
`I(X_i : Y_<i | X_<i, Y_≥i, D) = 0`. -/
theorem fixedAliceCrossInfoTerm_eq_zero (i : Fin n) :
    fixedAliceCrossInfoTerm n i = 0 := by
  rw [fixedAliceCrossInfoTerm]
  let ν := uniformDisjointCoordinateVector n
  have hpull :
      I[fixedXBit n i : fixedYBefore n i | fixedAliceConditioning n i ; disjointCondMeasure n] =
        I[coordinateXBit n i : coordinateYBefore n i | coordinateAliceConditioning n i ; ν] := by
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite
      (μ := disjointCondMeasure n) (μ' := ν)
      (X := fixedXBit n i) (Y := fixedYBefore n i) (Z := fixedAliceConditioning n i)
      (X' := coordinateXBit n i)
      (Y' := coordinateYBefore n i)
      (Z' := coordinateAliceConditioning n i)
      (by simpa [ν] using identDistrib_fixedAliceCrossInfoTriple_uniform n i)
  rw [hpull]
  exact uniformDisjointCoordinateVector_crossInfo_eq_zero n i

open Classical in
/-- Fixed-coordinate chain-rule inequality:
`I(X_i : M | X_<i,Y_≥i) ≤ I(X_i : M | X_<i,Y)`. -/
theorem fixedAliceInfoTerm_le_fixedAliceFullYInfoTerm
    (p : ProtocolType n)
    (i : Fin n) :
    fixedAliceInfoTerm n p i ≤ fixedAliceFullYInfoTerm n p i := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  let Xᵢ : HardSample n → Bool := fixedXBit n i
  let M : HardSample n → TranscriptType n p := message n p
  let Ypre : HardSample n → Fin n → Bool := fixedYBefore n i
  let A : HardSample n → (Fin n → Bool) × (Fin n → Bool) :=
    fixedAliceConditioning n i
  have hle_add :
      I[Xᵢ : M | A ; μ] ≤ I[Xᵢ : (fun ω => (Ypre ω, M ω)) | A ; μ] := by
    exact ProbabilityTheory.condMutualInfo_le_prod_right_snd
      (μ := μ) (X := Xᵢ) (Y := Ypre) (W := M) (Z := A)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      Measurable.of_discrete
  have hchain :
      I[Xᵢ : (fun ω => (Ypre ω, M ω)) | A ; μ] =
        I[Xᵢ : Ypre | A ; μ] + I[Xᵢ : M | (fun ω => (Ypre ω, A ω)) ; μ] := by
    exact ProbabilityTheory.condMutualInfo_prod_right_eq_add
      (μ := μ) (X := Xᵢ) (Y := Ypre) (W := M) (Z := A)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      Measurable.of_discrete
  have hcross : I[Xᵢ : Ypre | A ; μ] = 0 := by
    simpa [fixedAliceCrossInfoTerm, μ, Xᵢ, Ypre, A] using
      fixedAliceCrossInfoTerm_eq_zero n i
  have hrec :
      I[Xᵢ : M | (fun ω => (Ypre ω, A ω)) ; μ] =
        I[Xᵢ : M | fixedAliceFullYConditioning n i ; μ] := by
    have h := ProbabilityTheory.condMutualInfo_of_inj
      (μ := μ) (X := Xᵢ) (Y := M) (Z := fixedAliceFullYConditioning n i)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      (fixedAliceChainConditioningValue_injective n i)
    rw [fixedAliceChainConditioningValue_fixedAliceFullYConditioning] at h
    simpa [Function.comp_def, Xᵢ, M, Ypre, A] using h
  rw [fixedAliceInfoTerm, fixedAliceFullYInfoTerm]
  calc
    I[fixedXBit n i : message n p | fixedAliceConditioning n i ; disjointCondMeasure n]
        ≤ I[Xᵢ : (fun ω => (Ypre ω, M ω)) | A ; μ] := by
          simpa [μ, Xᵢ, M, A] using hle_add
    _ = I[Xᵢ : Ypre | A ; μ] + I[Xᵢ : M | (fun ω => (Ypre ω, A ω)) ; μ] :=
          hchain
    _ = I[fixedXBit n i : message n p | fixedAliceFullYConditioning n i ;
            disjointCondMeasure n] := by
          rw [hcross, zero_add, hrec]

open Classical in
/-- Summing the fixed-coordinate inequalities. -/
theorem sum_fixedAliceInfoTerm_le_sum_fixedAliceFullYInfoTerm
    (p : ProtocolType n) :
    (∑ i : Fin n, fixedAliceInfoTerm n p i) ≤
      ∑ i : Fin n, fixedAliceFullYInfoTerm n p i := by
  exact Finset.sum_le_sum fun i _ => fixedAliceInfoTerm_le_fixedAliceFullYInfoTerm n p i

open Classical in
/-- Chain rule for the full Alice vector:
`∑ᵢ I(X_i : M | X_<i,Y,D) = I(X : M | Y,D)`. -/
theorem sum_fixedAliceFullYInfoTerm_eq_xVector_info
    (p : ProtocolType n) :
    (∑ i : Fin n, fixedAliceFullYInfoTerm n p i) =
      I[xVector n : message n p | yVector n ; disjointCondMeasure n] := by
  have hchain := ProbabilityTheory.condMutualInfo_boolVector_eq_sum_strictPrefix
    (μ := disjointCondMeasure n) (X := xVector n) (Y := message n p) (Z := yVector n)
    Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
  rw [hchain]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold fixedAliceFullYInfoTerm fixedAliceFullYConditioning fixedXStrictPrefix fixedXBit xVector
    ProbabilityTheory.boolVectorStrictPrefix
  rfl

open Classical in
/-- Chain-rule step for the Alice summands:
`∑ᵢ I(X_i : M | X_<i, Y_≥i, D) ≤ I(X : M | Y, D)`.

Its only probabilistic input is `fixedAliceCrossInfoTerm_eq_zero`. -/
theorem sum_fixedAliceInfoTerm_le_xVector_info
    (p : ProtocolType n) :
    (∑ i : Fin n, fixedAliceInfoTerm n p i) ≤
      I[xVector n : message n p | yVector n ; disjointCondMeasure n] := by
  calc
    (∑ i : Fin n, fixedAliceInfoTerm n p i)
        ≤ ∑ i : Fin n, fixedAliceFullYInfoTerm n p i :=
          sum_fixedAliceInfoTerm_le_sum_fixedAliceFullYInfoTerm n p
    _ = I[xVector n : message n p | yVector n ; disjointCondMeasure n] :=
          sum_fixedAliceFullYInfoTerm_eq_xVector_info n p

open Classical in
/-- Expanding Alice's random-coordinate information term by the special coordinate `T`. -/
theorem aliceInfoTerm_eq_sum_specialCoordinate_fiber_info
    (p : ProtocolType n) :
    aliceInfoTerm n p =
      ∑ i : Fin n,
        (1 / (n : ℝ) : ℝ) *
          I[specialX n : message n p | aliceDynamicConditioning n ;
            (disjointCondMeasure n)[|specialCoordinate n ← i]] := by
  rw [aliceInfoTerm, aliceClaimConditioning_eq_specialCoordinate_prod_dynamic]
  rw [ProbabilityTheory.condMutualInfo_prod_conditioning_eq_sum
    (μ := disjointCondMeasure n)
    (X := specialX n) (Y := message n p)
    (K := specialCoordinate n) (Z := aliceDynamicConditioning n)
    Measurable.of_discrete Measurable.of_discrete]
  simp_rw [disjointCondMeasure_measureReal_specialCoordinate_preimage_singleton]

open Classical in
/-- Uniformity/independence step for the special coordinate: after conditioning on
`T=i`, the random-coordinate Alice information term is the fixed-coordinate summand. -/
theorem aliceDynamicConditioning_fiber_info_eq_fixedAliceInfoTerm
    (p : ProtocolType n) (i : Fin n) :
    I[specialX n : message n p | aliceDynamicConditioning n ;
      (disjointCondMeasure n)[|specialCoordinate n ← i]] =
      fixedAliceInfoTerm n p i := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  let μi : Measure (HardSample n) := μ[|specialCoordinate n ← i]
  let ν : Measure (Fin n → DisjointCoordinate) :=
    uniformDisjointCoordinateVector n
  haveI : IsProbabilityMeasure μi := by
    dsimp [μi, μ]
    apply ProbabilityTheory.cond_isProbabilityMeasure
    rw [← MeasureTheory.measureReal_ne_zero_iff]
    rw [disjointCondMeasure_measureReal_specialCoordinate_preimage_singleton]
    positivity
  have hspecial_fixed : specialX n =ᵐ[μi] fixedXBit n i := by
    dsimp [μi, μ]
    filter_upwards [ae_cond_mem MeasurableSet.of_discrete] with ω hω
    have hT : ω.T = i := by
      simpa [specialCoordinate] using hω
    simp [specialX, fixedXBit, xBit, hT]
  have hspecial_coord :
      specialX n =ᵐ[μi]
        fun ω => coordinateXBit n i (disjointCoordinateVector n ω) := by
    exact hspecial_fixed.trans
      (by
        simpa [μi, μ] using
          (cond_absolutelyContinuous.ae_le (fixedXBit_ae_eq_coordinateXBit n i)))
  have hmessage_coord_cond :
      message n p =ᵐ[μi]
        fun ω => coordinateMessage n p (disjointCoordinateVector n ω) := by
    simpa [μi, μ] using
      (cond_absolutelyContinuous.ae_le (message_ae_eq_coordinateMessage n p))
  have hdyn_fixed :
      aliceDynamicConditioning n =ᵐ[μi] fixedAliceConditioning n i := by
    dsimp [μi, μ]
    filter_upwards [ae_cond_mem MeasurableSet.of_discrete] with ω hω
    have hT : ω.T = i := by
      simpa [specialCoordinate] using hω
    ext j <;>
      simp [aliceDynamicConditioning, fixedAliceConditioning, xBeforeSpecial,
        yGeSpecial, fixedXBefore, fixedYGe, hT]
  have hdyn_coord :
      aliceDynamicConditioning n =ᵐ[μi]
        fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω) := by
    exact hdyn_fixed.trans
      (by
        simpa [μi, μ] using
          (cond_absolutelyContinuous.ae_le
            (fixedAliceConditioning_ae_eq_coordinateAliceConditioning n i)))
  have hleft_congr :
      I[specialX n : message n p | aliceDynamicConditioning n ; μi] =
        I[(fun ω => coordinateXBit n i (disjointCoordinateVector n ω)) :
          (fun ω => coordinateMessage n p (disjointCoordinateVector n ω)) |
          (fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω)) ; μi] := by
    exact ProbabilityTheory.condMutualInfo_congr_ae_finite
      (μ := μi)
      (X := specialX n) (Y := message n p) (Z := aliceDynamicConditioning n)
      (X' := fun ω => coordinateXBit n i (disjointCoordinateVector n ω))
      (Y' := fun ω => coordinateMessage n p (disjointCoordinateVector n ω))
      (Z' := fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω))
      hspecial_coord hmessage_coord_cond hdyn_coord
  have hleft_pull :
      I[(fun ω => coordinateXBit n i (disjointCoordinateVector n ω)) :
          (fun ω => coordinateMessage n p (disjointCoordinateVector n ω)) |
          (fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω)) ; μi] =
        I[coordinateXBit n i : coordinateMessage n p | coordinateAliceConditioning n i ; ν] := by
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite
      (μ := μi) (μ' := ν)
      (X := fun ω => coordinateXBit n i (disjointCoordinateVector n ω))
      (Y := fun ω => coordinateMessage n p (disjointCoordinateVector n ω))
      (Z := fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω))
      (X' := coordinateXBit n i)
      (Y' := coordinateMessage n p)
      (Z' := coordinateAliceConditioning n i)
      (by
        simpa [Function.comp_def, μi, μ, ν] using
          (identDistrib_disjointCoordinateVector_uniform_cond_specialCoordinate n i).comp
            (Measurable.of_discrete
            (f := fun coords =>
              (coordinateXBit n i coords, coordinateMessage n p coords,
                coordinateAliceConditioning n i coords))))
  have hright_congr :
      fixedAliceInfoTerm n p i =
        I[(fun ω => coordinateXBit n i (disjointCoordinateVector n ω)) :
          (fun ω => coordinateMessage n p (disjointCoordinateVector n ω)) |
          (fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω)) ; μ] := by
    rw [fixedAliceInfoTerm]
    exact ProbabilityTheory.condMutualInfo_congr_ae_finite
      (μ := μ)
      (X := fixedXBit n i) (Y := message n p) (Z := fixedAliceConditioning n i)
      (X' := fun ω => coordinateXBit n i (disjointCoordinateVector n ω))
      (Y' := fun ω => coordinateMessage n p (disjointCoordinateVector n ω))
      (Z' := fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω))
      (fixedXBit_ae_eq_coordinateXBit n i)
      (message_ae_eq_coordinateMessage n p)
      (fixedAliceConditioning_ae_eq_coordinateAliceConditioning n i)
  have hright_pull :
      I[(fun ω => coordinateXBit n i (disjointCoordinateVector n ω)) :
          (fun ω => coordinateMessage n p (disjointCoordinateVector n ω)) |
          (fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω)) ; μ] =
        I[coordinateXBit n i : coordinateMessage n p | coordinateAliceConditioning n i ; ν] := by
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite
      (μ := μ) (μ' := ν)
      (X := fun ω => coordinateXBit n i (disjointCoordinateVector n ω))
      (Y := fun ω => coordinateMessage n p (disjointCoordinateVector n ω))
      (Z := fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω))
      (X' := coordinateXBit n i)
      (Y' := coordinateMessage n p)
      (Z' := coordinateAliceConditioning n i)
      (by
        simpa [Function.comp_def, ν] using
          (identDistrib_disjointCoordinateVector_uniform n).comp
            (Measurable.of_discrete
            (f := fun coords =>
              (coordinateXBit n i coords, coordinateMessage n p coords,
                coordinateAliceConditioning n i coords))))
  calc
    I[specialX n : message n p | aliceDynamicConditioning n ;
        (disjointCondMeasure n)[|specialCoordinate n ← i]]
        = I[specialX n : message n p | aliceDynamicConditioning n ; μi] := by
          rfl
    _ = I[coordinateXBit n i : coordinateMessage n p | coordinateAliceConditioning n i ; ν] :=
          hleft_congr.trans hleft_pull
    _ = fixedAliceInfoTerm n p i := (hright_congr.trans hright_pull).symm

open Classical in
/-- Averaging over the special coordinate: conditioned on `D`, `T` is uniform and independent of
`(X,Y,M)`, so the Alice term is the average of the fixed-coordinate summands. -/
theorem aliceInfoTerm_eq_average_fixedAliceInfoTerm
    (p : ProtocolType n) :
    aliceInfoTerm n p =
      (∑ i : Fin n, fixedAliceInfoTerm n p i) / (n : ℝ) := by
  rw [aliceInfoTerm_eq_sum_specialCoordinate_fiber_info]
  simp_rw [aliceDynamicConditioning_fiber_info_eq_fixedAliceInfoTerm]
  rw [← Finset.mul_sum]
  ring

open Classical in
/-- Alice fixed-coordinate chain-rule bound after conditioning on disjointness and averaging over
the uniform
special coordinate:
`I(X_T : M | T, X_<T, Y_≥T, D) ≤ I(X : M | Y, D) / n`. -/
theorem aliceInfoTerm_le_average_xVector_info
    (p : ProtocolType n) :
    aliceInfoTerm n p ≤
      I[xVector n : message n p | yVector n ; disjointCondMeasure n] / (n : ℝ) := by
  rw [aliceInfoTerm_eq_average_fixedAliceInfoTerm]
  exact div_le_div_of_nonneg_right (sum_fixedAliceInfoTerm_le_xVector_info n p) (by positivity)

open Classical in
/-- Bob fixed-coordinate chain-rule bound after conditioning on disjointness and averaging over
the uniform
special coordinate:
`I(Y_T : M | T, X_≤T, Y_>T, D) ≤ I(Y : M | X, D) / n`. -/
theorem bobInfoTerm_le_average_yVector_info
    (p : ProtocolType n) :
    bobInfoTerm n p ≤
      I[yVector n : message n p | xVector n ; disjointCondMeasure n] / (n : ℝ) := by
  have h := aliceInfoTerm_le_average_xVector_info n (dualProtocol n p)
  simpa [aliceInfoTerm_dualProtocol_eq_bobInfoTerm,
    xVector_message_info_dualProtocol_eq_yVector_message_info] using h

open Classical in
/-- The Alice full-vector information is bounded by the transcript entropy. -/
theorem xVector_message_info_le_complexity_mul_log_two
    (p : ProtocolType n) :
    I[xVector n : message n p | yVector n ; disjointCondMeasure n] ≤
      p.complexity * Real.log 2 := by
  exact
    (ProbabilityTheory.condMutualInfo_le_entropy_right
      (μ := disjointCondMeasure n)
      (X := xVector n) (Y := message n p) (Z := yVector n)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete).trans
      (entropy_message_le_complexity_mul_log_two_of_measure n p (disjointCondMeasure n))

open Classical in
/-- The Bob full-vector information is bounded by the transcript entropy. -/
theorem yVector_message_info_le_complexity_mul_log_two
    (p : ProtocolType n) :
    I[yVector n : message n p | xVector n ; disjointCondMeasure n] ≤
      p.complexity * Real.log 2 := by
  exact
    (ProbabilityTheory.condMutualInfo_le_entropy_right
      (μ := disjointCondMeasure n)
      (X := yVector n) (Y := message n p) (Z := xVector n)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete).trans
      (entropy_message_le_complexity_mul_log_two_of_measure n p (disjointCondMeasure n))

open Classical in
/-- Alice's averaged fixed-coordinate information plus the entropy bound `H(M) ≤ ℓ`. -/
theorem aliceInfoTerm_le_average_entropy_bound
    (p : ProtocolType n) :
    aliceInfoTerm n p ≤ (p.complexity * Real.log 2) / (n : ℝ) := by
  have hchain := aliceInfoTerm_le_average_xVector_info n p
  have hentropy := xVector_message_info_le_complexity_mul_log_two n p
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  exact hchain.trans (div_le_div_of_nonneg_right hentropy hn_nonneg)

open Classical in
/-- Bob's averaged fixed-coordinate information plus the entropy bound `H(M) ≤ ℓ`. -/
theorem bobInfoTerm_le_average_entropy_bound
    (p : ProtocolType n) :
    bobInfoTerm n p ≤ (p.complexity * Real.log 2) / (n : ℝ) := by
  have hchain := bobInfoTerm_le_average_yVector_info n p
  have hentropy := yVector_message_info_le_complexity_mul_log_two n p
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  exact hchain.trans (div_le_div_of_nonneg_right hentropy hn_nonneg)

/-- The corrected claim information is at most the averaged full-vector transcript information
coming from the entropy bound `H(M) ≤ ℓ`. -/
theorem claimInfo_le_average_info_upper
    (p : ProtocolType n) :
    claimInfo n p ≤ 2 * (p.complexity * Real.log 2) / (n : ℝ) := by
  rw [claimInfo]
  calc
    aliceInfoTerm n p + bobInfoTerm n p
        ≤ (p.complexity * Real.log 2) / (n : ℝ) +
            (p.complexity * Real.log 2) / (n : ℝ) :=
          add_le_add (aliceInfoTerm_le_average_entropy_bound n p)
            (bobInfoTerm_le_average_entropy_bound n p)
    _ = 2 * (p.complexity * Real.log 2) / (n : ℝ) := by ring

open Classical in
/-- On the branch `Y_T=false`, the corrected Alice suffix `Y_≥T` is the same information as
the coarse suffix `Y_>T`, since the missing coordinate is fixed to `false`. -/
theorem yGeSpecial_eq_yAfterSpecial_of_specialY_false
    {ω : HardSample n} (hY : specialY n ω = false) :
    yGeSpecial n ω = yAfterSpecial n ω := by
  funext j
  by_cases hlt : ω.T < j
  · have hle : ω.T ≤ j := le_of_lt hlt
    simp [yGeSpecial, yAfterSpecial, hle, hlt]
  · by_cases hle : ω.T ≤ j
    · have hEq : j = ω.T := le_antisymm (not_lt.mp hlt) hle
      subst j
      simp only [yGeSpecial, le_refl, ↓reduceIte, yBit, yAfterSpecial, lt_self_iff_false]
      change ω.yT = false at hY
      exact hY
    · simp [yGeSpecial, yAfterSpecial, hle, hlt]

open Classical in
/-- On the branch `Y_T=false`, Alice's corrected conditioning is exactly the coarse
conditioning from `Z=(M,T,X_<T,Y_>T)`. -/
theorem aliceClaimConditioning_eq_coarseConditioning_of_specialY_false
    {ω : HardSample n} (hY : specialY n ω = false) :
    aliceClaimConditioning n ω = coarseConditioning n ω := by
  simp [aliceClaimConditioning, coarseConditioning,
    yGeSpecial_eq_yAfterSpecial_of_specialY_false n hY]

open Classical in
/-- Under `D ∧ Y_T=false`, Bob's special bit is almost surely `false`. -/
theorem disjointSpecialYFalseMeasure_ae_specialY_false :
    ∀ᵐ ω ∂disjointSpecialYFalseMeasure n, specialY n ω = false := by
  rw [disjointSpecialYFalseMeasure]
  filter_upwards [ae_cond_mem MeasurableSet.of_discrete] with ω hω
  simpa using hω

open Classical in
/-- Under `D ∧ Y_T=false`, Alice's fine conditioning variable is a.e. the coarse conditioning
variable. -/
theorem aliceClaimConditioning_ae_eq_coarseConditioning_disjointSpecialYFalse :
    aliceClaimConditioning n =ᵐ[disjointSpecialYFalseMeasure n] coarseConditioning n := by
  filter_upwards [disjointSpecialYFalseMeasure_ae_specialY_false n] with ω hY
  exact aliceClaimConditioning_eq_coarseConditioning_of_specialY_false n hY

open Classical in
/-- The Alice information term after additionally conditioning on `Y_T=false`:
`I(X_T : M | T, X_<T, Y_≥T, Y_T=0, D)`. -/
noncomputable def aliceInfoTermSpecialYFalse
    (p : ProtocolType n) : ℝ :=
  I[specialX n : message n p | aliceClaimConditioning n ; disjointSpecialYFalseMeasure n]

open Classical in
/-- The same Alice `Y_T=false` information term using the coarse conditioning
`T, X_<T, Y_>T`. -/
noncomputable def aliceCoarseInfoTermSpecialYFalse
    (p : ProtocolType n) : ℝ :=
  I[specialX n : message n p | coarseConditioning n ; disjointSpecialYFalseMeasure n]

open Classical in
/-- Since `X_T` is uniform under `D ∧ Y_T=false`, the conditional KL average to the uniform bit
law is the mutual information between `X_T` and the full `Z=(M,T,X_<T,Y_>T)` variable. -/
theorem condKLDiv_specialX_zVariable_eq_mutualInfo_zVariable
    (p : ProtocolType n) :
    condKLDiv (specialX n) id (zVariable n p) (disjointSpecialYFalseMeasure n)
        uniformBool =
      I[specialX n : zVariable n p ; disjointSpecialYFalseMeasure n] := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  have hmap : Measure.map (specialX n) (disjointSpecialYFalseMeasure n) =
      uniformBool := by
    exact disjointSpecialYFalseMeasure_specialX_law_eq_uniformBool n
  have hKL0 :
      KL[specialX n ; disjointSpecialYFalseMeasure n # id ;
        uniformBool] = 0 := by
    simp [KLDiv, hmap]
  have hcond := condKLDiv_eq
    (μ := disjointSpecialYFalseMeasure n)
    (μ' := uniformBool)
    (X := specialX n) (Y := id) (Z := zVariable n p)
    Measurable.of_discrete Measurable.of_discrete
    (fun b hb => False.elim (uniformBool_toPMF_ne_zero b (by
      simpa [Measure.toPMF_apply] using hb)))
  rw [hKL0] at hcond
  rw [ProbabilityTheory.mutualInfo_eq_entropy_sub_condEntropy
    Measurable.of_discrete Measurable.of_discrete]
  simpa using hcond

open Classical in
/-- The fine `Y_≥T` and coarse `Y_>T` versions of the Alice `Y_T=false` information term agree,
because `Y_T` is fixed on the conditioned measure. -/
theorem aliceInfoTermSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse
    (p : ProtocolType n) :
    aliceInfoTermSpecialYFalse n p = aliceCoarseInfoTermSpecialYFalse n p := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  rw [aliceInfoTermSpecialYFalse, aliceCoarseInfoTermSpecialYFalse]
  exact ProbabilityTheory.condMutualInfo_congr_ae_finite
    (μ := disjointSpecialYFalseMeasure n)
    (X := specialX n) (Y := message n p) (Z := aliceClaimConditioning n)
    (X' := specialX n) (Y' := message n p) (Z' := coarseConditioning n)
    (by rfl) (by rfl) (aliceClaimConditioning_ae_eq_coarseConditioning_disjointSpecialYFalse n)

open Classical in
/-- The averaged Alice fiber KL cost under `D ∧ Y_T=false`, as a finite sum over `Z` values. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable
    (p : ProtocolType n) :
    (∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n)) =
      ∑ z : ZType n p,
        (disjointSpecialYFalseMeasure n).real (zFiber n p z) *
          xFiberKL n p z := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  exact FiniteMeasureSpace.integral_comp_eq_sum_measureReal_fibers
    (μ := disjointSpecialYFalseMeasure n) (Z := zVariable n p) (f := xFiberKL n p)

open Classical in
/-- The averaged Alice fiber KL cost under `D ∧ Y_T=false` as a finite sum of actual KL
divergences for the conditional `Z=z` laws. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable_klDiv
    (p : ProtocolType n) :
    (∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n)) =
      ∑ z : ZType n p,
        (disjointSpecialYFalseMeasure n).real (zFiber n p z) *
          (InformationTheory.klDiv
            (Measure.map (specialX n)
              ((disjointSpecialYFalseMeasure n)[|zVariable n p ← z]))
            uniformBool).toReal := by
  rw [integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : (disjointSpecialYFalseMeasure n).real (zFiber n p z) = 0
  · simp [hz]
  · rw [xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv_of_ne_zero n p z hz]

open Classical in
/-- The averaged Alice fiber KL under `D ∧ Y_T=false`, rewritten as the PFR real conditional KL
used by the entropy API. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_condKLDiv_zVariable
    (p : ProtocolType n) :
    (∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n)) =
      condKLDiv (specialX n) id (zVariable n p) (disjointSpecialYFalseMeasure n)
        uniformBool := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  rw [integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable_klDiv]
  rw [condKLDiv, tsum_fintype]
  apply Finset.sum_congr rfl
  intro z _
  dsimp [zFiber]
  by_cases hz :
      (disjointSpecialYFalseMeasure n).real ((zVariable n p) ⁻¹' {z}) = 0
  · simp [hz]
  · rw [ProbabilityTheory.toReal_klDiv_map_bool_eq_KLDiv_of_measureReal_ne_zero
      (μ := disjointSpecialYFalseMeasure n) (X := specialX n)
      (S := (zVariable n p) ⁻¹' {z}) uniformBool Measurable.of_discrete hz
      uniformBool_toPMF_ne_zero]

open Classical in
/-- Flip only Alice's special-coordinate bit.  This preserves the coarse conditioning data
`T, X_<T, Y_>T` and toggles `X_T`. -/
def flipSpecialX (ω : HardSample n) : HardSample n where
  T := ω.T
  xT := !ω.xT
  yT := ω.yT
  other := ω.other

theorem flipSpecialX_flipSpecialX (ω : HardSample n) :
    flipSpecialX n (flipSpecialX n ω) = ω := by
  rcases ω with ⟨T, xT, yT, other⟩
  cases xT <;> rfl

theorem flipSpecialX_preimage_singleton (ω : HardSample n) :
    (flipSpecialX n) ⁻¹' ({ω}) = {flipSpecialX n ω} := by
  ext η
  constructor
  · intro hη
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hη
    rw [← hη]
    simp [flipSpecialX_flipSpecialX]
  · intro hη
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hη ⊢
    rw [hη, flipSpecialX_flipSpecialX]

theorem volume_measureReal_singleton_flipSpecialX (ω : HardSample n) :
    volume.real ({flipSpecialX n ω} : Set (HardSample n)) =
      volume.real ({ω} : Set (HardSample n)) := by
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real
      ({flipSpecialX n ω} : Set (HardSample n))) =
    ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real
      ({ω} : Set (HardSample n)))
  repeat rw [Measure.real]
  rw [uniformOn_univ_measureReal_eq_card_subtype,
    uniformOn_univ_measureReal_eq_card_subtype]
  simp

theorem volume_measurePreserving_flipSpecialX :
    MeasurePreserving (flipSpecialX n)
      volume volume := by
  refine ⟨Measurable.of_discrete, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro ω
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real, flipSpecialX_preimage_singleton,
    volume_measureReal_singleton_flipSpecialX]

theorem specialX_flipSpecialX (ω : HardSample n) :
    specialX n (flipSpecialX n ω) = !specialX n ω := by
  simp [flipSpecialX, specialX]

theorem specialY_flipSpecialX (ω : HardSample n) :
    specialY n (flipSpecialX n ω) = specialY n ω := by
  simp [flipSpecialX, specialY]

theorem xBeforeSpecial_flipSpecialX (ω : HardSample n) :
    xBeforeSpecial n (flipSpecialX n ω) = xBeforeSpecial n ω := by
  funext i
  by_cases hlt : i < ω.T
  · have hi : i ≠ ω.T := ne_of_lt hlt
    simp [xBeforeSpecial, xBit, flipSpecialX, hlt, hi]
  · simp [xBeforeSpecial, flipSpecialX, hlt]

theorem yAfterSpecial_flipSpecialX (ω : HardSample n) :
    yAfterSpecial n (flipSpecialX n ω) = yAfterSpecial n ω := by
  funext i
  simp [yAfterSpecial, yBit, flipSpecialX]

theorem coarseConditioning_flipSpecialX (ω : HardSample n) :
    coarseConditioning n (flipSpecialX n ω) = coarseConditioning n ω := by
  unfold coarseConditioning
  rw [show specialCoordinate n (flipSpecialX n ω) = specialCoordinate n ω by
      simp [specialCoordinate, flipSpecialX],
    xBeforeSpecial_flipSpecialX, yAfterSpecial_flipSpecialX]

open Classical in
/-- In every `Y_T=false, coarse=c` fiber of the ambient hard distribution, each value of `X_T`
has half the mass. -/
theorem volume_measureReal_specialYFalse_inter_coarseConditioning_inter_specialX
    (b : Bool) (c : Fin n × (Fin n → Bool) × (Fin n → Bool)) :
    volume.real
        (((specialY n) ⁻¹' {false}) ∩ ((coarseConditioning n) ⁻¹' {c}) ∩
          ((specialX n) ⁻¹' {b})) =
      (1 / 2 : ℝ) *
        volume.real
          (((specialY n) ⁻¹' {false}) ∩ ((coarseConditioning n) ⁻¹' {c})) := by
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  let C : Set (HardSample n) := (coarseConditioning n) ⁻¹' {c}
  let XF : Set (HardSample n) := (specialX n) ⁻¹' {false}
  let XT : Set (HardSample n) := (specialX n) ⁻¹' {true}
  have hfalse_true :
      volume.real (Y0 ∩ C ∩ XF) =
        volume.real (Y0 ∩ C ∩ XT) := by
    have hpre : (flipSpecialX n) ⁻¹' (Y0 ∩ C ∩ XT) = Y0 ∩ C ∩ XF := by
      ext ω
      simp [Y0, C, XF, XT, specialY_flipSpecialX, coarseConditioning_flipSpecialX,
        specialX_flipSpecialX]
    have hpre_measure :
        volume ((flipSpecialX n) ⁻¹' (Y0 ∩ C ∩ XT)) =
          volume (Y0 ∩ C ∩ XT) :=
      Measure.measure_preimage_of_map_eq_self
        (volume_measurePreserving_flipSpecialX n).map_eq
        MeasurableSet.of_discrete.nullMeasurableSet
    rw [← hpre]
    simpa [Measure.real] using congrArg ENNReal.toReal hpre_measure
  have hunion : Y0 ∩ C = (Y0 ∩ C ∩ XF) ∪ (Y0 ∩ C ∩ XT) := by
    ext ω
    by_cases hx : specialX n ω = false
    · simp [Y0, C, XF, XT, hx]
    · have hxtrue : specialX n ω = true := by
        cases h : specialX n ω
        · exact False.elim (hx h)
        · rfl
      simp [Y0, C, XF, XT, hx]
  have hdisj : Disjoint (Y0 ∩ C ∩ XF) (Y0 ∩ C ∩ XT) := by
    rw [Set.disjoint_left]
    intro ω hF hT
    have hfalse : specialX n ω = false := by simpa [XF] using hF.2
    have htrue : specialX n ω = true := by simpa [XT] using hT.2
    rw [hfalse] at htrue
    simp at htrue
  have hsum :
      volume.real (Y0 ∩ C) =
        volume.real (Y0 ∩ C ∩ XF) +
          volume.real (Y0 ∩ C ∩ XT) := by
    simpa [← hunion] using
      (measureReal_union hdisj MeasurableSet.of_discrete :
        volume.real
            ((Y0 ∩ C ∩ XF) ∪ (Y0 ∩ C ∩ XT)) =
          volume.real (Y0 ∩ C ∩ XF) +
            volume.real (Y0 ∩ C ∩ XT))
  cases b
  · change volume.real (Y0 ∩ C ∩ XF) =
      (1 / 2 : ℝ) * volume.real (Y0 ∩ C)
    linarith
  · change volume.real (Y0 ∩ C ∩ XT) =
      (1 / 2 : ℝ) * volume.real (Y0 ∩ C)
    linarith

open Classical in
/-- The preceding ambient counting identity remains true after conditioning on `Y_T=false`. -/
theorem disjointSpecialYFalseMeasure_measureReal_specialX_inter_coarseConditioning
    (b : Bool) (c : Fin n × (Fin n → Bool) × (Fin n → Bool)) :
    (disjointSpecialYFalseMeasure n).real
        (((specialX n) ⁻¹' {b}) ∩ ((coarseConditioning n) ⁻¹' {c})) =
      (1 / 2 : ℝ) *
        (disjointSpecialYFalseMeasure n).real ((coarseConditioning n) ⁻¹' {c}) := by
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  let Xb : Set (HardSample n) := (specialX n) ⁻¹' {b}
  let C : Set (HardSample n) := (coarseConditioning n) ⁻¹' {c}
  have hleft :
      (disjointSpecialYFalseMeasure n).real (Xb ∩ C) =
        ((disjointCondMeasure n).real Y0)⁻¹ *
          (disjointCondMeasure n).real (Y0 ∩ (Xb ∩ C)) := by
    rw [disjointSpecialYFalseMeasure]
    exact ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete _ (Xb ∩ C)
  have hright :
      (disjointSpecialYFalseMeasure n).real C =
        ((disjointCondMeasure n).real Y0)⁻¹ *
          (disjointCondMeasure n).real (Y0 ∩ C) := by
    rw [disjointSpecialYFalseMeasure]
    exact ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete _ C
  have hbranch_volume :
      volume.real (Y0 ∩ C ∩ Xb) =
        (1 / 2 : ℝ) * volume.real (Y0 ∩ C) := by
    simpa [Y0, C, Xb, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      volume_measureReal_specialYFalse_inter_coarseConditioning_inter_specialX n b c
  have hbranch :
      (disjointCondMeasure n).real (Y0 ∩ C ∩ Xb) =
        (1 / 2 : ℝ) * (disjointCondMeasure n).real (Y0 ∩ C) := by
    rw [disjointCondMeasure]
    repeat rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
    have hY0C_subset_D : Y0 ∩ C ⊆ disjointEvent n := by
      intro ω hω
      exact mem_disjointEvent_of_specialY_eq_false n (by simpa [Y0] using hω.1)
    have hY0CX_subset_D : Y0 ∩ C ∩ Xb ⊆ disjointEvent n := by
      intro ω hω
      exact hY0C_subset_D ⟨hω.1.1, hω.1.2⟩
    rw [Set.inter_eq_right.mpr hY0CX_subset_D, Set.inter_eq_right.mpr hY0C_subset_D]
    rw [hbranch_volume]
    ring
  rw [hleft, hright]
  have hsets : Y0 ∩ (Xb ∩ C) = Y0 ∩ C ∩ Xb := by
    ext ω
    simp only [Set.mem_inter_iff]
    tauto
  rw [hsets, hbranch]
  ring

open Classical in
/-- Under `D ∧ Y_T=false`, the coarse data `T, X_<T, Y_>T` is independent of `X_T`.
This is the sampling independence used before adding the transcript rectangle. -/
theorem mutualInfo_specialX_coarseConditioning_disjointSpecialYFalse_eq_zero :
    I[specialX n : coarseConditioning n ; disjointSpecialYFalseMeasure n] = 0 := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  apply (ProbabilityTheory.mutualInfo_eq_zero Measurable.of_discrete Measurable.of_discrete).mpr
  apply ProbabilityTheory.indepFun_of_measureReal_inter_preimage_singleton_eq_mul
    (μ := μ) (X := specialX n) (Y := coarseConditioning n)
    Measurable.of_discrete Measurable.of_discrete
  intro b c
  rw [show
      μ.real ((specialX n) ⁻¹' {b} ∩ (coarseConditioning n) ⁻¹' {c}) =
        (disjointSpecialYFalseMeasure n).real
          (((specialX n) ⁻¹' {b}) ∩ ((coarseConditioning n) ⁻¹' {c})) by rfl]
  rw [disjointSpecialYFalseMeasure_measureReal_specialX_inter_coarseConditioning]
  rw [disjointSpecialYFalseMeasure_measureReal_specialX_singleton]

open Classical in
/-- The full `Z=(M,coarse)` mutual information is the coarse information term,
because the coarse part alone is independent of `X_T` under `D ∧ Y_T=false`. -/
theorem mutualInfo_specialX_zVariable_eq_aliceCoarseInfoTermSpecialYFalse
    (p : ProtocolType n) :
    I[specialX n : zVariable n p ; disjointSpecialYFalseMeasure n] =
      aliceCoarseInfoTermSpecialYFalse n p := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  let swappedZ :
      HardSample n → (Fin n × (Fin n → Bool) × (Fin n → Bool)) × TranscriptType n p :=
    fun ω => (coarseConditioning n ω, message n p ω)
  let swapZ :
      ZType n p →
        (Fin n × (Fin n → Bool) × (Fin n → Bool)) × TranscriptType n p :=
    fun z => ((z.specialCoordinate, z.xBefore, z.yAfter), z.transcript)
  have hswap_fun : swappedZ = swapZ ∘ zVariable n p := by
    funext ω
    simp [swappedZ, swapZ, zVariable, rawZVariable, message, coarseConditioning,
      ZType.specialCoordinate, ZType.xBefore, ZType.yAfter, ZType.transcript]
  have hrec :
      I[specialX n : swappedZ ; μ] =
        I[specialX n : zVariable n p ; μ] := by
    rw [hswap_fun]
    exact ProbabilityTheory.mutualInfo_comp_right_of_injective
      (μ := μ) (X := specialX n) (Y := zVariable n p)
      Measurable.of_discrete Measurable.of_discrete
      swapZ Measurable.of_discrete
      (by
        intro z z' h
        have h' := Prod.ext_iff.mp h
        apply ZType.ext
        · exact h'.2
        · exact congrArg Prod.fst h'.1
        · exact congrArg (fun c => c.2.1) h'.1
        · exact congrArg (fun c => c.2.2) h'.1)
  have hchain :
      I[specialX n : swappedZ ; μ] =
        I[specialX n : coarseConditioning n ; μ] +
          I[specialX n : message n p | coarseConditioning n ; μ] := by
    simpa [swappedZ, μ] using
      ProbabilityTheory.mutualInfo_prod_right_eq_add
        (μ := disjointSpecialYFalseMeasure n)
        (X := specialX n) (Y := coarseConditioning n) (W := message n p)
        Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
  calc
    I[specialX n : zVariable n p ; disjointSpecialYFalseMeasure n]
        = I[specialX n : swappedZ ; μ] := by
          simpa [μ] using hrec.symm
    _ = I[specialX n : coarseConditioning n ; μ] +
          I[specialX n : message n p | coarseConditioning n ; μ] := hchain
    _ = aliceCoarseInfoTermSpecialYFalse n p := by
          rw [mutualInfo_specialX_coarseConditioning_disjointSpecialYFalse_eq_zero]
          simp [aliceCoarseInfoTermSpecialYFalse, μ]

open Classical in
/-- KL identification with the coarse `Z` conditioning: the average Alice one-bit fiber KL is the
conditional mutual information
`I(X_T : M | T,X_<T,Y_>T,Y_T=0,D)`. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse
    (p : ProtocolType n) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) =
      aliceCoarseInfoTermSpecialYFalse n p := by
  rw [integral_xFiberKL_disjointSpecialYFalse_eq_condKLDiv_zVariable]
  rw [condKLDiv_specialX_zVariable_eq_mutualInfo_zVariable]
  exact mutualInfo_specialX_zVariable_eq_aliceCoarseInfoTermSpecialYFalse n p

open Classical in
/-- Identification of the average Alice one-bit fiber KL with the conditional mutual information
under `Y_T=false`.  This packages the step
`p(x_t | z) = p(x_t | z, y_t=0) = p(x_t | z, y_t=0, D)` coming from independence and the
rectangle property of the transcript. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_aliceInfoTermSpecialYFalse
    (p : ProtocolType n) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) =
      aliceInfoTermSpecialYFalse n p := by
  rw [aliceInfoTermSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse]
  exact integral_xFiberKL_disjointSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse n p

/-- Alice-side reweighting:
`(2/3) I(X_T : M | T, X_< T, Y_≥T, Y_T=0, D) ≤
 I(X_T : M | T, X_< T, Y_≥T, D)`.

The factor is `Pr[Y_T=false | D] = 2/3`, and the event `Y_T=false` is determined by the
conditioning variable because `Y_≥T` contains `Y_T`. -/
theorem two_thirds_mul_aliceInfoTermSpecialYFalse_le_aliceInfoTerm
    (p : ProtocolType n) :
    (2 / 3 : ℝ) * aliceInfoTermSpecialYFalse n p ≤ aliceInfoTerm n p := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointCondMeasure_isProbabilityMeasure n
  have hmass : μ.real Y0 = (2 / 3 : ℝ) := by
    simpa [μ, Y0] using disjointCondMeasure_measureReal_specialY_false n
  have hdet : Y0 = (aliceClaimConditioning n) ⁻¹' aliceClaimConditioningYFalseValues n := by
    simpa [Y0] using specialY_false_eq_preimage_aliceClaimConditioningYFalseValues n
  have h :=
    ProbabilityTheory.measureReal_mul_cond_condMutualInfo_le_condMutualInfo_of_event_eq_preimage
      (μ := μ)
      (X := specialX n) (Y := message n p) (Z := aliceClaimConditioning n)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      (A := Y0) (B := aliceClaimConditioningYFalseValues n)
      MeasurableSet.of_discrete hdet
  simpa [μ, Y0, hmass, aliceInfoTermSpecialYFalse, aliceInfoTerm,
    disjointSpecialYFalseMeasure] using h

/-- Alice information step under `D ∧ Y_T=false`: the average one-bit KL cost is bounded by
Alice's information term, with the `2/3` conditioning factor. -/
theorem integral_xFiberKL_disjointSpecialYFalse_le_three_halves_mul_aliceInfoTerm
    (p : ProtocolType n) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
      (3 / 2 : ℝ) * aliceInfoTerm n p := by
  rw [integral_xFiberKL_disjointSpecialYFalse_eq_aliceInfoTermSpecialYFalse]
  have h := two_thirds_mul_aliceInfoTermSpecialYFalse_le_aliceInfoTerm n p
  nlinarith

/-- Alice information step under `D ∧ Y_T=false`: the average one-bit KL cost is bounded by the
small total information assumption. -/
theorem integral_xFiberKL_disjointSpecialYFalse_le_two_mul_gamma_pow_four
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
      2 * γ ^ 4 := by
  have hkl :=
    integral_xFiberKL_disjointSpecialYFalse_le_three_halves_mul_aliceInfoTerm n p
  have hγ4_nonneg : 0 ≤ γ ^ 4 := by positivity
  linarith [aliceInfoTerm_le_claimInfo n p]

/-- Alice Pinsker/information step under `D ∧ Y_T=false`: the squared one-bit marginal distance
has average at most `γ^4`. This is the KL-to-information comparison from the inequality
`(2/3) I(X_T : M | T, X_<T, Y_≥T, Y_T=0, D) ≤ I(X_T : M | T, X_<T, Y_≥T, D)`. -/
theorem integral_xDistance_sq_disjointSpecialYFalse_le_gamma_pow_four
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    ∫ ω, (xDistance n p (zVariable n p ω)) ^ 2 ∂(disjointSpecialYFalseMeasure n) ≤
      γ ^ 4 := by
  have hpinsker :=
    two_mul_integral_xDistance_sq_le_integral_xFiberKL_disjointSpecialYFalse n p
  have hkl := integral_xFiberKL_disjointSpecialYFalse_le_two_mul_gamma_pow_four n p hγ hinfo
  nlinarith

open Classical in
/-- Alice marginal estimate: under the `(X_T,Y_T)=(0,0)` slice, the set of `Z` fibers
whose Alice special-bit marginal is farther than `γ` from uniform has mass at most `γ / 2`. -/
theorem measureReal_specialZeroZero_inter_xDistance_bad_le
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    volume.real
      (specialZeroZero n ∩ {ω | γ < xDistance n p (zVariable n p ω)}) ≤ γ / 2 := by
  let μ : Measure (HardSample n) := volume
  let badX : Set (HardSample n) := {ω | γ < xDistance n p (zVariable n p ω)}
  have hsquared :=
    integral_xDistance_sq_disjointSpecialYFalse_le_gamma_pow_four n p hγ hinfo
  have havg :
      ∫ ω, xDistance n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
        γ ^ 2 :=
    disjointSpecialYFalseMeasure_integral_xDistance_le_of_integral_sq_le n p hsquared
  have hbad_y0 :
      (disjointSpecialYFalseMeasure n).real badX ≤ γ := by
    simpa [badX] using
      disjointSpecialYFalseMeasure_xDistance_bad_le_of_integral_le n p hγ havg
  have htransfer :
      (μ[|specialZeroZero n]).real badX ≤ 2 * γ := by
    have h :=
      volume_cond_specialZeroZero_measureReal_le_two_mul_disjointSpecialYFalseMeasure n badX
    have hbad_y0_two :
        2 * (disjointSpecialYFalseMeasure n).real badX ≤ 2 * γ := by
      nlinarith
    exact h.trans (by simpa [μ] using hbad_y0_two)
  have hcond_eq :
      (μ[|specialZeroZero n]).real badX =
        (μ.real (specialZeroZero n))⁻¹ * μ.real (specialZeroZero n ∩ badX) := by
    rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hA : μ.real (specialZeroZero n) = (1 / 4 : ℝ) := by
    simpa [μ, Measure.real] using measureReal_specialZeroZero n
  change μ.real (specialZeroZero n ∩ badX) ≤ γ / 2
  rw [hcond_eq, hA] at htransfer
  norm_num at htransfer
  linarith

open Classical in
/-- Bob marginal estimate, symmetric to the Alice marginal estimate. -/
theorem measureReal_specialZeroZero_inter_yDistance_bad_le
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    volume.real
      (specialZeroZero n ∩ {ω | γ < yDistance n p (zVariable n p ω)}) ≤ γ / 2 := by
  have hinfoDual : claimInfo n (dualProtocol n p) ≤ 2 * γ ^ 4 / 3 := by
    simpa [claimInfo_dualProtocol n p] using hinfo
  have h :=
    measureReal_specialZeroZero_inter_xDistance_bad_le n (dualProtocol n p) hγ hinfoDual
  simpa [volume_specialZeroZero_inter_xDistance_dualProtocol_eq_yDistance n p γ] using h

/-- If the corrected special-coordinate information is `≤ 2γ^4 / 3`, then the set of `Z` fibers
where the conditional law of `(X_T, Y_T)` is within
`2γ` of uniform has hard-distribution mass at least `(1 - 4γ) / 4`. -/
theorem one_div_four_mul_one_sub_four_mul_le_measureReal_goodZEvent
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    (1 / 4 : ℝ) * (1 - 4 * γ) ≤
      volume.real (goodZEvent n p γ) := by
  let μ : Measure (HardSample n) := volume
  let A : Set (HardSample n) := specialZeroZero n
  let badX : Set (HardSample n) := {ω | γ < xDistance n p (zVariable n p ω)}
  let badY : Set (HardSample n) := {ω | γ < yDistance n p (zVariable n p ω)}
  have hxBad : μ.real (A ∩ badX) ≤ γ / 2 := by
    simpa [μ, A, badX] using measureReal_specialZeroZero_inter_xDistance_bad_le n p hγ hinfo
  have hyBad : μ.real (A ∩ badY) ≤ γ / 2 := by
    simpa [μ, A, badY] using measureReal_specialZeroZero_inter_yDistance_bad_le n p hγ hinfo
  have hA : μ.real A = (1 / 4 : ℝ) := by
    simpa [μ, A] using measureReal_specialZeroZero n
  have hcover : A ⊆ goodZEvent n p γ ∪ (A ∩ badX) ∪ (A ∩ badY) := by
    intro ω hωA
    by_cases hx : γ < xDistance n p (zVariable n p ω)
    · exact Or.inl (Or.inr ⟨hωA, hx⟩)
    · by_cases hy : γ < yDistance n p (zVariable n p ω)
      · exact Or.inr ⟨hωA, hy⟩
      · have hxle : xDistance n p (zVariable n p ω) ≤ γ := le_of_not_gt hx
        have hyle : yDistance n p (zVariable n p ω) ≤ γ := le_of_not_gt hy
        exact Or.inl (Or.inl (mem_goodZEvent_of_xDistance_yDistance_le n p hxle hyle))
  have hmono :
      μ.real A ≤ μ.real ((goodZEvent n p γ ∪ (A ∩ badX)) ∪ (A ∩ badY)) :=
    measureReal_mono hcover
  have hunion_outer :
      μ.real ((goodZEvent n p γ ∪ (A ∩ badX)) ∪ (A ∩ badY)) ≤
        μ.real (goodZEvent n p γ ∪ (A ∩ badX)) + μ.real (A ∩ badY) :=
    measureReal_union_le _ _
  have hunion_inner :
      μ.real (goodZEvent n p γ ∪ (A ∩ badX)) ≤
        μ.real (goodZEvent n p γ) + μ.real (A ∩ badX) :=
    measureReal_union_le _ _
  linarith

/-- Intersecting with the defining `Z=z` fiber does not change probabilities under the
corresponding fiber measure. -/
theorem zFiberMeasure_inter_fiber
    (p : ProtocolType n)
    (z : ZType n p)
    (S : Set (HardSample n)) :
    (zFiberMeasure n p z).real ((zFiber n p z) ∩ S) =
      (zFiberMeasure n p z).real S := by
  rw [zFiberMeasure]
  rw [Measure.real]
  rw [ProbabilityTheory.cond_inter_self MeasurableSet.of_discrete]
  rfl

open Classical in
/-- A good `z` gives the expected singleton-mass estimate for the conditional special-pair law. -/
theorem abs_conditionalSpecialPairLaw_singleton_sub_quarter_le
    (p : ProtocolType n)
    {γ : ℝ}
    {z : ZType n p}
    (hgood : goodZ n p γ z)
    (b : Bool × Bool) :
    |(conditionalSpecialPairLaw n p z :
        Measure (Bool × Bool)).real {b} - (1 / 4 : ℝ)| ≤ 2 * γ := by
  have htv :=
    TVDistance.abs_measureReal_sub_le_tvDistance
      (conditionalSpecialPairLaw n p z) uniformBoolPair
      ⟨({b} : Set (Bool × Bool)), MeasurableSet.of_discrete⟩
  rw [uniformBoolPair_singleton] at htv
  have hgood' :
      tvDistance (conditionalSpecialPairLaw n p z) uniformBoolPair ≤ 2 * γ := by
    simpa [goodZ, zDistance] using hgood
  exact htv.trans hgood'

/-- A good `z` gives a lower bound on each singleton mass of the conditional special-pair law. -/
theorem quarter_sub_two_mul_le_conditionalSpecialPairLaw_singleton
    (p : ProtocolType n)
    {γ : ℝ}
    {z : ZType n p}
    (hgood : goodZ n p γ z)
    (b : Bool × Bool) :
    (1 / 4 : ℝ) - 2 * γ ≤
      (conditionalSpecialPairLaw n p z :
        Measure (Bool × Bool)).real {b} := by
  have h := abs_conditionalSpecialPairLaw_singleton_sub_quarter_le n p hgood b
  rw [abs_le] at h
  linarith

/-- On a fixed `Z=z` fiber, inputs whose special pair equals the `Z`-determined protocol output
on both sides are protocol errors. -/
theorem zFiber_inter_diag_specialPair_subset_protocolErrorEvent
    (p : ProtocolType n)
    {z : ZType n p} :
    (zFiber n p z) ∩ ((specialPair n) ⁻¹' {(zOutput n p z, zOutput n p z)}) ⊆
      protocolErrorEvent n p := by
  intro ω' hω'
  let b := zOutput n p z
  have hrun' : p.run (X n ω') (Y n ω') = b := by
    simpa [b] using run_eq_zOutput_of_zVariable_eq n p (by simpa [zFiber] using hω'.1)
  have hpair : specialPair n ω' = (b, b) := by
    simpa [b] using hω'.2
  cases hb : b
  · have hbits : ω'.xT = false ∧ ω'.yT = false := by
      simpa [specialPair, specialX, specialY, hb] using hpair
    have hdisj : Disjoint (X n ω') (Y n ω') := by
      rw [disjoint_X_Y_iff]
      intro hboth
      rw [hbits.1] at hboth
      simp at hboth
    simp [protocolErrorEvent, disjointness, hrun', hdisj, hb]
  · have hbits : ω'.xT = true ∧ ω'.yT = true := by
      simpa [specialPair, specialX, specialY, hb] using hpair
    have hnot_disj : ¬Disjoint (X n ω') (Y n ω') := by
      rw [disjoint_X_Y_iff]
      exact not_not_intro hbits
    simp [protocolErrorEvent, disjointness, hrun', hnot_disj, hb]

/-- On a good `Z` fiber, the conditional protocol-error probability is at least
`1 / 4 - 2 * γ`. If the protocol output on the fiber is `true`, then the `(true, true)` special
bit-pair witnesses errors; otherwise `(false, false)` witnesses errors. -/
theorem quarter_sub_two_mul_le_zFiberMeasure_protocolErrorEvent
    (p : ProtocolType n)
    {γ : ℝ} {z : ZType n p}
    (hgood : goodZ n p γ z) :
    (1 / 4 : ℝ) - 2 * γ ≤
      (zFiberMeasure n p z).real (protocolErrorEvent n p) := by
  haveI : IsFiniteMeasure (zFiberMeasure n p z) := by
    rw [zFiberMeasure]
    infer_instance
  let b := zOutput n p z
  have hmass :=
    quarter_sub_two_mul_le_conditionalSpecialPairLaw_singleton n p hgood (b, b)
  have hsubset :
      (zFiber n p z) ∩ ((specialPair n) ⁻¹' {(b, b)}) ⊆ protocolErrorEvent n p :=
    by simpa [b] using zFiber_inter_diag_specialPair_subset_protocolErrorEvent n p (z := z)
  have hmono :
      (zFiberMeasure n p z).real ((zFiber n p z) ∩ ((specialPair n) ⁻¹' {(b, b)})) ≤
        (zFiberMeasure n p z).real (protocolErrorEvent n p) :=
    measureReal_mono hsubset
  rw [zFiberMeasure_inter_fiber] at hmono
  rw [← conditionalSpecialPairLaw_singleton n p z (b, b)] at hmono
  exact hmass.trans hmono

/-- Averaging the good-fiber error lower bound over all good `Z` fibers gives an unconditional
error lower bound. -/
theorem goodZEvent_mul_quarter_sub_two_mul_le_protocolErrorEvent
    (p : ProtocolType n)
    (γ : ℝ) :
    volume.real (goodZEvent n p γ) * ((1 / 4 : ℝ) - 2 * γ) ≤
      volume.real (protocolErrorEvent n p) := by
  rw [FiniteMeasureSpace.measureReal_eq_sum_cond_fiber_real
    (μ := volume) (Z := zVariable n p) (S := protocolErrorEvent n p)]
  unfold goodZEvent
  rw [FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z _
  by_cases hgood : goodZ n p γ z
  · simp only [hgood, ↓reduceIte]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact quarter_sub_two_mul_le_zFiberMeasure_protocolErrorEvent n p
      hgood
  · simp only [hgood, ↓reduceIte, one_div, zero_mul]
    positivity

/-- The final good-fiber error calculation, phrased using distributional error. -/
theorem goodZEvent_mul_quarter_sub_two_mul_le_distributionalError
    (p : ProtocolType n) (γ : ℝ) :
    volume.real (goodZEvent n p γ) * ((1 / 4 : ℝ) - 2 * γ) ≤
      p.distributionalError (inputDist n) (disjointness n) := by
  rw [distributionalError_inputDist_eq_protocolErrorEvent]
  exact goodZEvent_mul_quarter_sub_two_mul_le_protocolErrorEvent n p γ

/-- A deterministic protocol with distributional error at most `1 / 32` must reveal a constant
amount of the corrected special-coordinate information. -/
theorem one_div_32768_sq_lt_claimInfo_of_distributionalError_le
    (p : ProtocolType n)
    (herror : p.distributionalError (inputDist n) (disjointness n) ≤ 1 / 32) :
    (1 / 32768 : ℝ) ^ 2 < claimInfo n p := by
  by_contra hnot
  have hgood :=
    one_div_four_mul_one_sub_four_mul_le_measureReal_goodZEvent n p
      (γ := (1 / 64 : ℝ)) (by norm_num) (by linarith)
  have herror_lower :=
    goodZEvent_mul_quarter_sub_two_mul_le_distributionalError n p (1 / 64)
  linarith

/-- Deterministic fixed-error disjointness lower bound from the information estimate. -/
theorem const_mul_n_le_complexity_of_distributionalError_le
    (p : ProtocolType n)
    (herror : p.distributionalError (inputDist n) (disjointness n) ≤ 1 / 32) :
    ((1 / 32768 : ℝ) ^ 2) * (n : ℝ) / (3 * Real.log 2) ≤ p.complexity := by
  have hinfo_lt := one_div_32768_sq_lt_claimInfo_of_distributionalError_le n p herror
  have hupper := claimInfo_le_average_info_upper n p
  have hmain :
      (1 / 32768 : ℝ) ^ 2 < 2 * (p.complexity * Real.log 2) / (n : ℝ) :=
    hinfo_lt.trans_le hupper
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hlog_pos : 0 < 3 * Real.log 2 := by positivity
  have hcomplexity_nonneg : 0 ≤ (p.complexity : ℝ) := by
    exact_mod_cast Nat.zero_le p.complexity
  rw [div_le_iff₀ hlog_pos]
  rw [lt_div_iff₀ hn_pos] at hmain
  nlinarith

/-- Public-coin fixed-error lower bound from the deterministic distributional lower bound via
minimax. -/
theorem lt_publicCoin_communicationComplexity_disjointness_of_lt_const_mul_n
    {k : ℕ}
    (hk : (k : ℝ) <
      ((1 / 32768 : ℝ) ^ 2) * (n : ℝ) / (3 * Real.log 2)) :
    k < PublicCoin.communicationComplexity (disjointness n) (1 / 32 : ℝ) := by
  refine PublicCoin.lt_communicationComplexity_of_forall_distributionalError_gt
    (f := disjointness n) (ε := (1 / 32 : ℝ)) (n := k) (μ := inputDist n) ?_
  intro p hp
  by_contra hnot
  have herror : p.distributionalError (inputDist n) (disjointness n) ≤ 1 / 32 :=
    le_of_not_gt hnot
  have hlower := const_mul_n_le_complexity_of_distributionalError_le n p herror
  have hcomplexity_real : (p.complexity : ℝ) ≤ k := by
    exact_mod_cast hp
  linarith

/-- Headline theorem: public-coin randomized communication complexity of disjointness is linear at
fixed error `1 / 32`, with a concrete conservative constant. The cutoff is the floor of the
real number `n / 2^32`, so the asymptotic constant is stated over the reals. -/
theorem floor_div_pow_lt_publicCoin_communicationComplexity_disjointness
    : Nat.floor ((n : ℝ) / (2 ^ 32 : ℝ)) <
      PublicCoin.communicationComplexity (disjointness n) (1 / 32 : ℝ) := by
  apply lt_publicCoin_communicationComplexity_disjointness_of_lt_const_mul_n n
  have hlog_lt_one : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    linarith
  have hscaled :
      (n : ℝ) / (2 ^ 32 : ℝ) <
        ((1 / 32768 : ℝ) ^ 2) * (n : ℝ) / (3 * Real.log 2) := by
    field_simp
    linarith
  exact (Nat.floor_le (by positivity)).trans_lt hscaled

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
