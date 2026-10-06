/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.FuncDisjointness
import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import TCSlib.CommunicationComplexity.DeterministicCC.Transcript
import Mathlib.Probability.UniformOn
import PFR.Mathlib.Probability.UniformOn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Disjointness lower bound: the hard sample space

The explicit finite sample space carrying Razborov's hard distribution for set
disjointness, as used in the information-complexity proof of the linear randomized lower
bound [RY20, Thm 6.13]. A sample consists of a uniformly random special coordinate `T`, two
independent uniform bits at `T`, and, at every other coordinate, a uniformly random pair
from `{00, 01, 10}`; the ambient probability measure is uniform on this finite type. This
file also defines the one-factor uniform laws, the accessors turning a sample into Alice's
and Bob's inputs, the basic events (`disjointEvent`, `specialIntersect`, …), and the
conditioning variables `(T, X_{<T}, Y_{>T})`, `(T, X_{<T}, Y_{≥T})`, `(T, X_{≤T}, Y_{>T})`
used in the chain-rule and rectangle arguments of later files.

## Main definitions

* `DisjointCoordinate`: the three disjoint coordinate pairs `00`, `10`, `01`.
* `HardSample`: the sample space `(T, xT, yT, other)` of the hard distribution, with its
  uniform `MeasureSpace` instance.
* `uniformFin`, `uniformBool`, `uniformDisjointCoordinateVector`,
  `uniformDisjointCoordinate`: the uniform laws on the factors of the sample space.
* `xBit`, `yBit`, `X`, `Y`, `xVector`, `yVector`, `input`: Alice's and Bob's inputs read
  off a sample.
* `reverseBoolVector`, `reverseSet`, `dualConditioningValue`: the coordinate-reversal /
  Alice–Bob swap recodings used for the symmetry argument.
* `specialIntersect`, `specialBitsEvent`, `specialCoordinateEvent`, `specialZeroZero`,
  `disjointEvent`: the basic events on the sample space.
* `specialCoordinate`, `specialX`, `specialY`, `xBeforeSpecial`, `xLeSpecial`,
  `yAfterSpecial`, `yGeSpecial`, `coarseConditioning`, `aliceClaimConditioning`,
  `bobClaimConditioning`: the conditioning variables of the special coordinate.
* `fixedXBit`, `fixedXStrictPrefix`, `fixedXBefore`, `fixedYBefore`, `fixedYGe`,
  `fixedAliceConditioning`, `fixedAliceFullYConditioning`,
  `fixedAliceChainConditioningValue`: their fixed-coordinate counterparts for the chain rule.

## Main results

* `HardSample.card`: the sample space has `n · 4 · 3^n` elements.
* `uniformFin_singleton`, `uniformBool_singleton`, `uniformDisjointCoordinate_singleton`,
  `uniformDisjointCoordinateVector_singleton`, and the `*_real` / `*_univ` variants: point
  masses and total mass of the factor laws.
* `fixedAliceChainConditioningValue_injective`,
  `fixedAliceChainConditioningValue_fixedAliceFullYConditioning`: the chain-rule recoding of
  `(X_{<i}, Y)` is injective and equals `(Y_{<i}, X_{<i}, Y_{≥i})` on samples.
* `specialY_false_eq_preimage_aliceClaimConditioningYFalseValues`: the event `Y_T = 0` is
  determined by Alice's conditioning variable.
* `dualConditioningValue_dualConditioningValue`, `dualConditioningValue_injective`: the
  conditioning-value duality is an involution.

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

noncomputable instance setFinFiniteMeasureSpace :
    FiniteMeasureSpace (Set (Fin n)) :=
  FiniteMeasureSpace.of (Set (Fin n))

/-- The three possible disjoint coordinate-pairs `(A_i, B_i) ∈ {(0,0), (1,0), (0,1)}` used at
every coordinate `i` other than the special coordinate `T`
[RY20, Ch. 6, §Randomized Communication of Disjointness: 'Hard distribution']; historically
[Raz92]. -/
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

/-- The sample space for the hard distribution: a special coordinate `T`, Alice's and Bob's
bits `xT`, `yT` at `T`, and a disjoint coordinate-pair at every other coordinate. Under the
uniform measure on this type, `T` is uniform, `(xT, yT)` are independent uniform bits, and
the pairs `(A_i, B_i)` for `i ≠ T` are independent and uniform on `{00, 01, 10}`
[RY20, Ch. 6, §Randomized Communication of Disjointness: 'Hard distribution']; historically
[Raz92]. The `other` coordinate at `T` is ignored; keeping it in the sample space makes the
ambient type a simple product-like finite type. -/
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

/-- We use the uniform distribution on the explicit hard-distribution sample space; this is
Razborov's hard distribution
[RY20, Ch. 6, §Randomized Communication of Disjointness: 'Hard distribution']; historically
[Raz92]. -/
noncomputable instance measureSpace : MeasureSpace (HardSample n) :=
  ⟨ProbabilityTheory.uniformOn Set.univ⟩

noncomputable instance isProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure (HardSample n)) := by
  change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
  infer_instance

noncomputable instance finiteProbabilitySpace : FiniteProbabilitySpace (HardSample n) :=
  FiniteProbabilitySpace.of (HardSample n)

/-- The hard sample space is in bijection with the product
`Fin n × Bool × Bool × (Fin n → DisjointCoordinate)` of its four fields, by sending a sample
`ω` to `(ω.T, ω.xT, ω.yT, ω.other)`. -/
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

/-- The explicit hard-distribution sample space has exactly `n · 4 · 3^n` elements: `n` choices
of the special coordinate, `4` choices of the two special bits, and `3^n` disjoint
coordinate vectors. -/
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

/-- The uniform law on disjoint coordinate vectors `Fin n → DisjointCoordinate`, i.e. the
product of independent uniform choices from `{00, 01, 10}` at every coordinate
[RY20, Ch. 6, §Randomized Communication of Disjointness: 'Hard distribution']; historically
[Raz92]. -/
noncomputable def uniformDisjointCoordinateVector :
    Measure (Fin n → DisjointCoordinate) :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable instance uniformDisjointCoordinateVector_isProbabilityMeasure :
    IsProbabilityMeasure (uniformDisjointCoordinateVector n) := by
  rw [uniformDisjointCoordinateVector]
  infer_instance

/-- The uniform law on one disjoint coordinate, giving mass `1/3` to each of `00`, `01`, `10`
[RY20, Ch. 6, §Randomized Communication of Disjointness: 'Hard distribution']; historically
[Raz92]. -/
noncomputable def uniformDisjointCoordinate :
    Measure DisjointCoordinate :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable instance uniformDisjointCoordinate_isProbabilityMeasure :
    IsProbabilityMeasure uniformDisjointCoordinate := by
  rw [uniformDisjointCoordinate]
  infer_instance

/-- The subtype of a singleton set has exactly one element (for any `Fintype` instance on it). -/
private theorem card_subtype_singleton_eq_one {α : Type*} (a : α)
    [Fintype {x : α // x ∈ ({a} : Set α)}] :
    Fintype.card {x : α // x ∈ ({a} : Set α)} = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨⟨a, rfl⟩, fun x => Subtype.ext x.2⟩

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
  -- Step 1: uniform mass is the singleton subtype cardinality over the ambient cardinality.
  rw [uniformOn_univ_measureReal_eq_card_subtype, card_subtype_singleton_eq_one coords]
  -- Step 2: the ambient cardinality is `3 ^ n`.
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
  -- Step 1: uniform mass is the singleton subtype cardinality over the ambient cardinality.
  rw [uniformOn_univ_measureReal_eq_card_subtype, card_subtype_singleton_eq_one c]
  -- Step 2: the ambient cardinality is `3`.
  simp [DisjointCoordinate.card]

/-- Alice's bit `A_i` at coordinate `i` under a hard-distribution sample: the special bit
`xT` if `i = T`, otherwise Alice's side of the disjoint pair at `i`
[RY20, Ch. 6, 'Hard distribution'] (`A`, `B` as bit strings). -/
def xBit (ω : HardSample n) (i : Fin n) : Bool :=
  if i = ω.T then ω.xT else (ω.other i).xBit

/-- Bob's bit `B_i` at coordinate `i` under a hard-distribution sample: the special bit `yT`
if `i = T`, otherwise Bob's side of the disjoint pair at `i`
[RY20, Ch. 6, 'Hard distribution'] (`A`, `B` as bit strings). -/
def yBit (ω : HardSample n) (i : Fin n) : Bool :=
  if i = ω.T then ω.yT else (ω.other i).yBit

/-- Alice's input set `A = {i | A_i = 1}` under a hard-distribution sample
[RY20, Ch. 6, 'Hard distribution'] (`A`, `B` as bit strings). -/
def X (ω : HardSample n) : Set (Fin n) :=
  {i | xBit n ω i = true}

/-- Bob's input set `B = {i | B_i = 1}` under a hard-distribution sample
[RY20, Ch. 6, 'Hard distribution'] (`A`, `B` as bit strings). -/
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

/-- The input pair `(A, B)` of sets generated by a hard-distribution sample
[RY20, Ch. 6, 'Hard distribution'] (`A`, `B` as bit strings). -/
def input (ω : HardSample n) : Set (Fin n) × Set (Fin n) :=
  (X n ω, Y n ω)

/-- The event that both special bits are `1`, i.e. that `T ∈ A ∩ B`; since the inputs
intersect in at most one element, this is exactly the event that `A` and `B` intersect
[RY20, Ch. 6, 'Hard distribution'] (`A`, `B` intersect in at most one element, namely
`T`). -/
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

/-- The event that the generated input sets `A` and `B` are disjoint
[RY20, Ch. 6, 'Hard distribution'] (`A`, `B` intersect in at most one element, namely
`T`). -/
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

/-- The special coordinate `T` selected by the hard distribution, the first component of the
conditioning variables `Q = (T, A_{<T}, B_{>T})` and `(T, A_{<T}, B_{≥T})`
[RY20, Ch. 6, eq. (6.3)]. -/
def specialCoordinate (ω : HardSample n) : Fin n :=
  ω.T

/-- Alice's bit `A_T` at the special coordinate, the variable whose information about the
transcript is bounded in [RY20, Ch. 6, eq. (6.3)]. -/
def specialX (ω : HardSample n) : Bool :=
  ω.xT

/-- Bob's bit `B_T` at the special coordinate, the extra conditioning variable in
[RY20, Ch. 6, eq. (6.3)]. -/
def specialY (ω : HardSample n) : Bool :=
  ω.yT

/-- Alice's input bits `A_{<T}` before the special coordinate, padded by `false` elsewhere;
a component of the conditioning variables `Q = (T, A_{<T}, B_{>T})` and
`(T, A_{<T}, B_{≥T})` [RY20, Ch. 6, eq. (6.3)]. -/
def xBeforeSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if i < ω.T then xBit n ω i else false

/-- Alice's input bits `A_{≤T}` up to and including the special coordinate, padded by
`false` elsewhere; the Alice component of Bob's conditioning variable `(T, A_{≤T}, B_{>T})`,
the mirror image of `(T, A_{<T}, B_{≥T})` in [RY20, Ch. 6, eq. (6.3)]. -/
def xLeSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if i ≤ ω.T then xBit n ω i else false

/-- Bob's input bits `B_{>T}` after the special coordinate, padded by `false` elsewhere; the
Bob component of `Q = (T, A_{<T}, B_{>T})` [RY20, Ch. 6, eq. (6.3)]. -/
def yAfterSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if ω.T < i then yBit n ω i else false

/-- Bob's input bits `B_{≥T}` from the special coordinate onward, padded by `false`
elsewhere; the Bob component of `(T, A_{<T}, B_{≥T})` [RY20, Ch. 6, eq. (6.3)]. -/
def yGeSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if ω.T ≤ i then yBit n ω i else false

/-- The common coarse conditioning variable `Q = (T, X_{<T}, Y_{>T})` used for
special-coordinate fibers [RY20, Ch. 6, eq. (6.3)]. -/
def coarseConditioning (ω : HardSample n) :
    Fin n × (Fin n → Bool) × (Fin n → Bool) :=
  (specialCoordinate n ω, xBeforeSpecial n ω, yAfterSpecial n ω)

/-- Alice's corrected special-coordinate conditioning variable `(T, X_{<T}, Y_{≥T})`, i.e.
`Q` together with Bob's special bit `Y_T` [RY20, Ch. 6, eq. (6.3)]. -/
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

/-- Bob's corrected special-coordinate conditioning variable `(T, X_{≤T}, Y_{>T})`, i.e.
`Q` together with Alice's special bit `X_T`; the Alice/Bob mirror image of the variable
`(T, A_{<T}, B_{≥T})` in [RY20, Ch. 6, eq. (6.3)]. -/
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

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
