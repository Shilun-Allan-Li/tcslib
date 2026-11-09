/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.ZVariable

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Disjointness lower bound: the disjoint model and mixing

Two combinatorial ingredients of the proof of [RY20, Thm 6.13], both stated at the level of
the hard sample space.

The first is the *mix-and-match* witness behind [RY20, Claim 6.14] ("fixing `S` restricts the
inputs to a rectangle"): from two hard samples that agree on the conditioning data
`(T, X_<T, Y_>T)` one builds a third sample, `mix`, carrying Alice's input from the first and
Bob's input from the second. Away from `T` this needs the requested bit pair to be one of the
three disjoint pairs, which `coordinateOfBits` encodes; the projection lemmas for `mix` live in
`DualHardSample`.

The second is the *disjoint model*: on the event `𝒟` that `A` and `B` are disjoint, a hard
sample is determined by its special coordinate `T`, a full vector of disjoint coordinate-pairs
(the pair at `T` being read off the special bits), and the ignored `other` value at `T`. This
recoding identifies the disjoint samples with a product `Fin n × (Fin n → DisjointCoordinate)
× DisjointCoordinate` on which the hard distribution is uniform, which is the formal content
of "conditioned on `𝒟`, `T` is independent of `A, B`"
[RY20, Ch. 6, 'Let 𝒟 be the event that A, B are disjoint'].

## Main definitions

- `coordinateOfBits`: the disjoint coordinate-pair with prescribed Alice/Bob bits.
- `mix`: the mixed sample with Alice's input from one sample and Bob's from another.
- `disjointCoordinateVector`, `ignoredCoordinate`, `disjointModel`: the components of the
  disjoint model and the model itself.

## Main results

- `xBit_of_ne_special`, `yBit_of_ne_special`, `not_xBit_and_yBit_of_ne_special`: away from
  `T` the input bits come from `other` and are never both `true`.
- `disjoint_X_Y_iff`: the generated sets are disjoint iff the special bits are not both `true`.
- `disjointCoordinateVector_xBit_of_mem_disjointEvent`,
  `disjointCoordinateVector_yBit_of_mem_disjointEvent`: on `𝒟` the model vector recovers
  both input bits at every coordinate.
- `card_disjointEvent_inter_disjointModel_fiber`,
  `measureReal_disjointEvent_inter_disjointModel_fiber`: inside `𝒟`, each fibre of the
  disjoint model is a single sample, of mass `1 / (4 n 3 ^ n)`.

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

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Functions.Disjointness

namespace RandomizedLowerBound

variable (n : ℕ+)

/-- Away from the special coordinate, Alice's bit at `i` is the Alice-bit of the disjoint
coordinate-pair `other i` of the sample. -/
theorem xBit_of_ne_special (ω : HardSample n) {i : Fin n} (hi : i ≠ ω.T) :
    xBit n ω i = (ω.other i).xBit := by
  simp [xBit, hi]

/-- Away from the special coordinate, Bob's bit at `i` is the Bob-bit of the disjoint
coordinate-pair `other i` of the sample. -/
theorem yBit_of_ne_special (ω : HardSample n) {i : Fin n} (hi : i ≠ ω.T) :
    yBit n ω i = (ω.other i).yBit := by
  simp [yBit, hi]

/-- Away from the special coordinate, Alice's and Bob's bits at `i` are never both `true`: the
generated sets can only intersect at `T` [RY20, Ch. 6, 'Hard distribution']. -/
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

/-- The mixed sample: the hard sample with special coordinate and Alice's special bit taken from
`ωX`, Bob's special bit taken from `ωY`, and at every other coordinate the disjoint pair whose
Alice-bit is `ωX`'s and whose Bob-bit is `ωY`'s. This is the mix-and-match witness for
"fixing `S` restricts the inputs to a rectangle" in the proof of [RY20, Claim 6.14]: it
realises the input `(X ωX, Y ωY)` of the rectangle spanned by two samples. It is only intended
to be used when the two samples agree on `T`, `X_<T`, and `Y_>T`; under those hypotheses the
mixed coordinate requests are always disjoint (`not_xBit_left_and_yBit_right_of_same_conditioning`
in `DualHardSample`), so the arbitrary default of `coordinateOfBits` is never hit. -/
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

/-- The disjoint model of a hard sample: the triple consisting of the special coordinate `T`,
the generated vector of disjoint coordinate-pairs, and the ignored `other` value at `T`. On the
disjoint event `𝒟` this triple determines the sample, and the map is a bijection from `𝒟` onto
the product type; since the hard distribution is uniform on samples, the three components are
independent and uniform given `𝒟`, which is the fact "conditioned on `𝒟`, `T` is independent
of `A, B`" of [RY20, Ch. 6, 'Let 𝒟 be the event that A, B are disjoint']. -/
def disjointModel (ω : HardSample n) :
    Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate :=
  (ω.T, disjointCoordinateVector n ω, ignoredCoordinate n ω)

/-- The disjoint samples are in bijection with `Fin n × (Fin n → DisjointCoordinate) ×
DisjointCoordinate`, the forward map being `disjointModel`.

**Construction.** The inverse sends `(T, coords, junk)` to the sample with special coordinate
`T`, special bits read off `coords T`, and `other := update coords T junk`; it lands in `𝒟`
because `coords T` is a disjoint pair (`disjoint_X_Y_iff`). Left inverse: on a disjoint sample
the special bits are not both `true`, so `coordinateOfBits` recovers them
(`coordinateOfBits_xBit`/`_yBit`), and away from `T` the updated vector agrees with `other`
while at `T` it is the ignored value. Right inverse: at `T` the model vector is
`coordinateOfBits (xBit c) (yBit c) = c` (`coordinateOfBits_xBit_yBit`), elsewhere it is
`coords i`, and the ignored value is `junk`. -/
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
    -- Step 1: a disjoint sample has special bits not both `true`.
    have hbits : ¬(xT = true ∧ yT = true) := by
      simpa [disjoint_X_Y_iff] using hω
    -- Step 2: compare the four fields; the special bits are recovered by `coordinateOfBits`,
    -- and the updated vector agrees with `other` away from `T` and at `T`.
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
    -- Step 3: the model of the rebuilt sample is `(T, coords, junk)` componentwise.
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

/-- Inside the disjoint event, the fibre of the disjoint model above any value `z` is a
singleton: it is in bijection with `Unit`. The unique element is the disjoint sample obtained
from `z` by the inverse of `disjointEventEquiv`; uniqueness is injectivity of that
equivalence. -/
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

/-- Inside the disjoint event, each fibre of the disjoint model consists of exactly one hard
sample: for every model value `z`, exactly one disjoint sample has model `z`. -/
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
/-- Inside the disjoint event `𝒟`, the fibre of the disjoint model above any value `z` has
hard-distribution mass `1 / (4 n 3 ^ n)`, the mass of a single sample. Since this mass does not
depend on `z`, the model `(T, coordinate vector, ignored value)` is uniform on its product range
given `𝒟`; in particular `T` is independent of `(A, B)` conditioned on `𝒟`
[RY20, Ch. 6, 'Let 𝒟 be the event that A, B are disjoint']. -/
theorem measureReal_disjointEvent_inter_disjointModel_fiber
    (z : Fin n × (Fin n → DisjointCoordinate) × DisjointCoordinate) :
    volume.real (disjointEvent n ∩ (disjointModel n) ⁻¹' {z}) =
      (1 / ((n : ℝ) * 4 * 3 ^ (n : ℕ)) : ℝ) := by
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n))
      (disjointEvent n ∩ (disjointModel n) ⁻¹' {z})).toReal =
    (1 / ((n : ℝ) * 4 * 3 ^ (n : ℕ)) : ℝ)
  rw [uniformOn_univ_measureReal_eq_card_subtype,
    card_disjointEvent_inter_disjointModel_fiber, HardSample.card]
  norm_num [Nat.cast_mul, Nat.cast_pow]

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
