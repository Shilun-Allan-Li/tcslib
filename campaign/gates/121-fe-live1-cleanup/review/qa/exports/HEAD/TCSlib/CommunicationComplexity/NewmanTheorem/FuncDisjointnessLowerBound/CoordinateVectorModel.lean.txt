/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.HardDistributionEvents

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Disjointness lower bound: the coordinate vector model

The proof of [RY20, Thm 6.13] applies the chain-rule inequality [RY20, Lemma 6.15] to the
law `p(ab | 𝒟)`, whose hypothesis is that the coordinate pairs `(A_i, B_i)` are mutually
independent. On the hard sample space this is awkward to state directly, so this file recasts
the relevant random variables on the *coordinate vector model*: the product space
`Fin n → DisjointCoordinate` carrying the uniform product law
`uniformDisjointCoordinateVector`. It defines the coordinate projections (`coordinateXBit`,
`coordinateYBefore`, `coordinateAliceConditioning`, …), proves there the independence input
`I(X_i : Y_{<i} | X_{<i} Y_{≥i}) = 0` used in the proof of Lemma 6.15
(`uniformDisjointCoordinateVector_crossInfo_eq_zero`), and transfers it back to the hard
sample space: under `𝒟` the generated coordinate vector `disjointCoordinateVector` has
exactly the uniform law, independently of the special coordinate `T` (the `identDistrib_*`
family), and the fixed-coordinate variables of `HardSample` agree almost surely with their
coordinate-vector counterparts (the `*_ae_eq_*` lemmas).

## Main definitions

* `coordinateXBit`, `coordinateYBit`, `coordinateXSet`, `coordinateYSet`,
  `coordinateInput`, `coordinateMessage`: Alice's and Bob's bits, sets, input pair and
  transcript read off a disjoint coordinate vector.
* `coordinateXBefore`, `coordinateYBefore`, `coordinateYGe`,
  `coordinateAliceConditioning`: the padded prefix/suffix projections `X_{<i}`, `Y_{<i}`,
  `Y_{≥i}` and the pair `(X_{<i}, Y_{≥i})`.
* `coordinateAliceCondBit`, `coordinateAliceCondBits`, `coordinateAliceResidualBit`,
  `coordinateAliceConditioningOfCondBits`: the one-bit-per-coordinate recoding of
  `(X_{<i}, Y_{≥i})`, the complementary residual bits, and the recoding back to the padded
  pair.
* `coordinateWithCondBit`: a disjoint pair realising a prescribed conditioning bit.

## Main results

* `coordinateAliceConditioning_eq_recode_condBits`,
  `coordinateAliceConditioningOfCondBits_injective`: `(X_{<i}, Y_{≥i})` is an injective
  recoding of the one-bit-per-coordinate conditioning.
* `uniformDisjointCoordinateVector_residual_cond_iIndepFun`,
  `uniformDisjointCoordinateVector_indep_coordinateXBit_coordinateYBefore_condBits`: the
  per-coordinate (residual, conditioning) pairs are independent, and given the conditioning
  bits `X_i` is independent of `Y_{<i}`.
* `uniformDisjointCoordinateVector_crossInfo_condBits_eq_zero`,
  `uniformDisjointCoordinateVector_crossInfo_eq_zero`: `I(X_i : Y_{<i} | X_{<i} Y_{≥i}) = 0`
  under the uniform law.
* `fixedXBit_ae_eq_coordinateXBit`, `fixedYBefore_ae_eq_coordinateYBefore`,
  `fixedAliceConditioning_ae_eq_coordinateAliceConditioning`: on `𝒟` the fixed-coordinate
  variables of the sample space are the coordinate-vector projections.
* `identDistrib_specialCoordinate_disjointCoordinateVector_uniform_prod`,
  `identDistrib_disjointCoordinateVector_uniform`,
  `identDistrib_disjointCoordinateVector_uniform_cond_specialCoordinate`: under `𝒟` the
  pair `(T, coords)` is uniform, so `coords` is uniform, also after conditioning on `T = i`.
* `identDistrib_fixedAliceCrossInfoTriple_uniform`: the triple `(X_i, Y_{<i}, (X_{<i}, Y_{≥i}))`
  has the same law under `𝒟` as its coordinate-vector version under the uniform law.

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

/-- The coordinate-vector version of Alice's fixed-coordinate conditioning: the padded pair
`(X_{<i}, Y_{≥i})` read off a disjoint coordinate vector. -/
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

/-- Alice's padded-pair conditioning `(X_{<i}, Y_{≥i})` is the composite of the
one-bit-per-coordinate conditioning with the recoding `coordinateAliceConditioningOfCondBits`.
-/
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

/-- The event that the one-bit-per-coordinate conditioning equals a prescribed vector `bits`
is the intersection over all coordinates `k` of the single-bit events
`coordinateAliceCondBit i k = bits k`. -/
theorem coordinateAliceCondBits_fiber_eq_iInter (i : Fin n) (bits : Fin n → Bool) :
    (coordinateAliceCondBits n i) ⁻¹' {bits} =
      ⋂ k : Fin n, (coordinateAliceCondBit n i k) ⁻¹' {bits k} := by
  ext coords
  simp [coordinateAliceCondBits, funext_iff]

/-- A disjoint coordinate pair whose conditioning bit at position `k` (Alice's bit if
`k < i`, Bob's bit otherwise) is the prescribed value `b`, with the other bit `0`; it
witnesses that every conditioning-bit event is nonempty. -/
def coordinateWithCondBit (i k : Fin n) (b : Bool) : DisjointCoordinate :=
  if k < i then
    if b then DisjointCoordinate.leftOnly else DisjointCoordinate.neither
  else
    if b then DisjointCoordinate.rightOnly else DisjointCoordinate.neither

/-- The pair `coordinateWithCondBit i k b` has conditioning bit `b` at position `k`: its
Alice bit is `b` when `k < i`, and its Bob bit is `b` otherwise. -/
theorem coordinateWithCondBit_spec (i k : Fin n) (b : Bool) :
    (if k < i then (coordinateWithCondBit n i k b).xBit
      else (coordinateWithCondBit n i k b).yBit) = b := by
  by_cases hlt : k < i <;> cases b <;>
    simp [coordinateWithCondBit, hlt, DisjointCoordinate.xBit, DisjointCoordinate.yBit]

open Classical in
/-- Under the uniform disjoint-vector law, the event that the conditioning bit at a single
coordinate `k` equals a prescribed value `b` has nonzero mass.

**Proof sketch.** It suffices to show the event has nonzero real mass. (1) Build a witness
vector: `neither` at every coordinate except `k`, where it is `coordinateWithCondBit i k b`;
by `coordinateWithCondBit_spec` its conditioning bit at `k` is `b`, so it lies in the event.
(2) The singleton of the witness is contained in the event and has positive mass under the
uniform law (`uniformDisjointCoordinateVector_singleton`), so by monotonicity the event has
positive mass. -/
theorem uniformDisjointCoordinateVector_measure_condBit_ne_zero
    (i k : Fin n) (b : Bool) :
    uniformDisjointCoordinateVector n ((coordinateAliceCondBit n i k) ⁻¹' {b}) ≠ 0 := by
  rw [← MeasureTheory.measureReal_ne_zero_iff]
  let coords : Fin n → DisjointCoordinate :=
    Function.update (fun _ => DisjointCoordinate.neither) k (coordinateWithCondBit n i k b)
  -- Step 1: the witness vector lies in the event
  have hmem : coords ∈ (coordinateAliceCondBit n i k) ⁻¹' ({b} : Set Bool) := by
    simp [coords, coordinateAliceCondBit, coordinateXBit, coordinateYBit,
      coordinateWithCondBit_spec]
  have hsubset : ({coords} : Set (Fin n → DisjointCoordinate)) ⊆
      (coordinateAliceCondBit n i k) ⁻¹' ({b} : Set Bool) := by
    intro coords' hcoords'
    rw [Set.mem_singleton_iff] at hcoords'
    subst coords'
    exact hmem
  -- Step 2: its singleton has positive mass, and the event contains it
  have hsingle_pos :
      0 < (uniformDisjointCoordinateVector n).real ({coords} : Set _) := by
    rw [uniformDisjointCoordinateVector_singleton]
    positivity
  have hle :=
    measureReal_mono (μ := uniformDisjointCoordinateVector n) hsubset
  exact ne_of_gt (hsingle_pos.trans_le hle)

open Classical in
/-- Under the uniform disjoint-vector law, the `n` pairs (residual bit, conditioning bit) at
the coordinates `k` are mutually independent, since each pair is a function of the `k`-th
coordinate alone and the coordinates are independent. -/
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
/-- Under the uniform disjoint-vector law conditioned on any value `bits` of Alice's
one-bit-per-coordinate conditioning `(X_{<i}, Y_{≥i})`, Alice's bit `X_i` is independent of
Bob's earlier bits `Y_{<i}`; this is the independence input to the chain-rule argument
[RY20, Lemma 6.15 proof] (`I(X_i : Y_{<i} | X_{<i} Y_{≥i}) = 0`).

**Proof sketch.** Step 1: write the conditioning event as the intersection over `k` of the
single-coordinate events `condBit_k = bits k`. Step 2: the per-coordinate pairs
`(residual_k, condBit_k)` are mutually independent and each single-coordinate event has
positive mass, so conditioning on all of them at once leaves the residual bits mutually
independent (`iIndepFun.cond`). Step 3: hence the residual bit at the index set `{i}` is
independent of the tuple of residual bits over `S = {k < i}` (`iIndepFun.indepFun_finset`,
the two index sets being disjoint). Step 4: composing with the measurable recodings that read
off the bit at `i` and spread the bits over `k < i` (padding by `false`) preserves
independence. Step 5: these composites are exactly `X_i` (the residual at `i` is Alice's bit)
and `Y_{<i}` (the residuals before `i` are Bob's bits), and `IndepFun.congr` transports
the independence along the two equalities. -/
theorem uniformDisjointCoordinateVector_indep_coordinateXBit_coordinateYBefore_condBits
    (i : Fin n) (bits : Fin n → Bool) :
    IndepFun (coordinateXBit n i) (coordinateYBefore n i)
      ((uniformDisjointCoordinateVector n :
        Measure (Fin n → DisjointCoordinate))[|(coordinateAliceCondBits n i) ⁻¹' {bits}]) := by
  let μ : Measure (Fin n → DisjointCoordinate) :=
    uniformDisjointCoordinateVector n
  -- Step 1: the conditioning event is an intersection of single-coordinate events.
  rw [coordinateAliceCondBits_fiber_eq_iInter]
  let S : Finset (Fin n) := Finset.univ.filter fun k => k < i
  -- Step 2: the residual bits stay mutually independent after conditioning.
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
  -- Step 3: the residual at `{i}` is independent of the residuals over `S = {k < i}`.
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
  -- Step 4: recode both sides; independence is preserved by measurable maps.
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
  -- Step 5: the recoded variables are `X_i` and `Y_{<i}`.
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
/-- Under the uniform disjoint-vector law, the conditional mutual information between
Alice's bit `X_i` and Bob's earlier bits `Y_{<i}` given Alice's one-bit-per-coordinate
conditioning (`X_k` for `k < i`, `Y_k` for `k ≥ i`) is zero; this is the independence input
`I(X_i : Y_{<i} | X_{<i} Y_{≥i}) = 0` of [RY20, Lemma 6.15 proof], stated with the
one-bit-per-coordinate conditioning variable. -/
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
/-- Under the uniform disjoint-vector law, the conditional mutual information between
Alice's bit `X_i` and Bob's earlier bits `Y_{<i}` given the padded pair `(X_{<i}, Y_{≥i})`
is zero: `I(X_i : Y_{<i} | X_{<i} Y_{≥i}) = 0`, the independence input of
[RY20, Lemma 6.15 proof]. It follows from the one-bit-per-coordinate version because the
padded pair is an injective recoding of the conditioning bits. -/
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
/-- Almost surely under the disjoint-conditioned law, Alice's fixed bit `X_i` on the sample
space equals Alice's bit at `i` of the generated disjoint coordinate vector. -/
theorem fixedXBit_ae_eq_coordinateXBit (i : Fin n) :
    fixedXBit n i =ᵐ[disjointCondMeasure n]
      fun ω => coordinateXBit n i (disjointCoordinateVector n ω) := by
  filter_upwards [disjointCondMeasure_ae_disjointEvent n] with ω hω
  exact (disjointCoordinateVector_xBit_of_mem_disjointEvent n hω i).symm

open Classical in
/-- Almost surely under the disjoint-conditioned law, Bob's fixed prefix `Y_{<i}` on the
sample space equals the `Y_{<i}` projection of the generated disjoint coordinate vector. -/
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
/-- Almost surely under the disjoint-conditioned law, Alice's fixed conditioning
`(X_{<i}, Y_{≥i})` on the sample space equals the corresponding projection of the generated
disjoint coordinate vector. -/
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
/-- Under the disjoint-conditioned law, the pair `(T, coords)` of the special coordinate and
the generated disjoint coordinate vector has the product law of the uniform distribution on
`Fin n` and the uniform disjoint-vector law: `T` is uniform and independent of the
coordinate vector, which is uniform [RY20, Ch. 6, 'conditioned on 𝒟, T is independent of
A, B'].

**Proof sketch.** Step 1: both laws live on a finite type, so it suffices to compare the
masses of the singletons `{(i, c)}`; the pushforward mass of `{(i, c)}` is the conditional
mass of the event `T = i ∧ coords = c`. Step 2: that mass is `1 / (n · 3 ^ n)` by
`disjointCondMeasure_measureReal_specialCoordinate_disjointCoordinateVector_fiber`.
Step 3: the product-law mass of `{(i, c)} = {i} ×ˢ {c}` is `(1 / n) · (1 / 3 ^ n)`, which
agrees. -/
theorem identDistrib_specialCoordinate_disjointCoordinateVector_uniform_prod :
    IdentDistrib
      (fun ω : HardSample n => (specialCoordinate n ω, disjointCoordinateVector n ω))
      id
      (disjointCondMeasure n)
      ((uniformFin n).prod (uniformDisjointCoordinateVector n)) := by
  refine ⟨Measurable.of_discrete.aemeasurable, measurable_id.aemeasurable, ?_⟩
  -- Step 1: compare singleton masses; the pushforward mass is the mass of `T = i ∧ coords = c`.
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
  -- Step 2: the conditional mass of the event is `1 / (n · 3 ^ n)`.
  rw [disjointCondMeasure_measureReal_specialCoordinate_disjointCoordinateVector_fiber]
  -- Step 3: the product-law mass of `{i} ×ˢ {c}` is `(1 / n) · (1 / 3 ^ n)`.
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
/-- The second marginal of the product law `uniformFin n ⊗ uniformDisjointCoordinateVector n`
is the uniform disjoint-vector law: `Prod.snd` under the product law is distributed as the
identity under `uniformDisjointCoordinateVector n`. -/
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
/-- Under the disjoint-conditioned law, the generated disjoint coordinate vector has the
uniform disjoint-vector law: it is distributed as the identity under
`uniformDisjointCoordinateVector n` [RY20, Ch. 6, 'conditioned on 𝒟, T is independent of
A, B'] (the coordinate-vector marginal of the product law). -/
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
/-- Conditioning the product law `uniformFin n ⊗ uniformDisjointCoordinateVector n` on the
first component being `i` leaves the second component with the uniform disjoint-vector law.

**Proof sketch.** Compare the masses of singletons `{c}`: the pushforward of the conditioned
product law under `Prod.snd` gives the ratio `ρ(fst = i ∧ snd = c) / ρ(fst = i)`.
Step 1: the denominator is the mass of `{i} ×ˢ univ`, namely `1 / n`. Step 2: the numerator
is the mass of `{i} ×ˢ {c}`, namely `1 / (n · 3 ^ n)`. Step 3: the ratio is `1 / 3 ^ n`,
the uniform singleton mass. -/
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
  -- Step 1: the conditioning event `fst = i` has product mass `1 / n`.
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
  -- Step 2: the event `fst = i ∧ snd = c` has product mass `1 / (n · 3 ^ n)`.
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
  -- Step 3: the ratio is the uniform singleton mass `1 / 3 ^ n`.
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
/-- The triple `(X_i, Y_{<i}, (X_{<i}, Y_{≥i}))` of fixed-coordinate variables on the sample
space has, under the disjoint-conditioned law, the same joint law as the corresponding triple
of coordinate-vector projections under the uniform disjoint-vector law.

**Proof sketch.** Step 1: almost surely under `𝒟`, the sample-space triple equals the
coordinate-vector triple evaluated at the generated coordinate vector (the three `*_ae_eq_*`
lemmas). Step 2: the generated coordinate vector is uniform under `𝒟`
(`identDistrib_disjointCoordinateVector_uniform`), and composing an identity of laws with a
measurable map yields the claim. -/
theorem identDistrib_fixedAliceCrossInfoTriple_uniform (i : Fin n) :
    IdentDistrib
      (fun ω : HardSample n =>
        (fixedXBit n i ω, fixedYBefore n i ω, fixedAliceConditioning n i ω))
      (fun coords : Fin n → DisjointCoordinate =>
        (coordinateXBit n i coords, coordinateYBefore n i coords,
          coordinateAliceConditioning n i coords))
      (disjointCondMeasure n)
      (uniformDisjointCoordinateVector n) := by
  -- Step 1: the sample-space triple is a.e. the coordinate-vector triple of `coords`.
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
  -- Step 2: transport along the a.e. equality and the uniform law of `coords`.
  exact
    (IdentDistrib.of_ae_eq Measurable.of_discrete.aemeasurable hfixed_coord).trans
      ((identDistrib_disjointCoordinateVector_uniform n).comp
        (Measurable.of_discrete
          (f := fun coords : Fin n → DisjointCoordinate =>
            (coordinateXBit n i coords, coordinateYBefore n i coords,
              coordinateAliceConditioning n i coords))))

open Classical in
/-- Under the disjoint-conditioned law further conditioned on `T = i`, the generated disjoint
coordinate vector still has the uniform disjoint-vector law; this is the independence of `T`
from the coordinate vector [RY20, Ch. 6, 'conditioned on 𝒟, T is independent of A, B'].

**Proof sketch.** Step 1: swapping the two components of the product-law identity shows that
`(coords, T)` under `𝒟` is distributed as `(snd, fst)` under
`ρ = uniformFin n ⊗ uniformDisjointCoordinateVector n`. Step 2: identically distributed pairs
remain identically distributed after conditioning both on the same event of their second
component (`IdentDistrib.cond_of_pair`), so `coords` under `𝒟 ∧ T = i` is distributed as
`snd` under `ρ[|fst = i]`. Step 3: the latter is the uniform disjoint-vector law
(`identDistrib_uniformProd_snd_uniformDisjointCoordinateVector_cond_fst`). -/
theorem identDistrib_disjointCoordinateVector_uniform_cond_specialCoordinate (i : Fin n) :
    IdentDistrib (disjointCoordinateVector n) id
      ((disjointCondMeasure n)[|specialCoordinate n ← i])
      (uniformDisjointCoordinateVector n) := by
  let ρ : Measure (Fin n × (Fin n → DisjointCoordinate)) :=
    (uniformFin n).prod (uniformDisjointCoordinateVector n)
  -- Step 1: `(coords, T)` under `𝒟` is `(snd, fst)` under the product law.
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
  -- Step 2: condition both pairs on the second component being `i`.
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
  -- Step 3: the conditioned product law has uniform second component.
  exact hcond.trans
    (by
      simpa [ρ] using
        identDistrib_uniformProd_snd_uniformDisjointCoordinateVector_cond_fst n i)

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
