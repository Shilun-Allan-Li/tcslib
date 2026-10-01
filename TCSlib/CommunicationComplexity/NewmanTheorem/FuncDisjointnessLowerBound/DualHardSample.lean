/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.DisjointModel

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Disjointness lower bound: Alice/Bob duality on samples

The proof of [RY20, Thm 6.13] bounds the information the transcript reveals about `A_T` and
disposes of the `B_T` case by a symmetric argument (the 'WLOG' step leading to eq. (6.2)). This
file provides the sample-level half of that symmetry: the involution `dualHardSample`, which
swaps Alice's and Bob's roles and reverses the coordinate order, together with transport
lemmas describing how each piece of a hard sample (bits, sets, special bits, windowed
conditioning vectors, corrected conditionings) behaves under it. Combined with `dualProtocol`
(in `ZVariable`), these let every Alice-side statement be transferred to Bob's side instead of
being reproved.

The file also proves the projection lemmas for `mix` (defined in `DisjointModel`): when two
samples agree on `(T, X_<T, Y_>T)`, the mixed sample carries Alice's input from the first and
Bob's input from the second, keeps the shared conditioning data, and mixing back recovers the
first sample. This is the rectangle property behind [RY20, Claim 6.14].

## Main definitions

- `dualHardSample`: the Alice/Bob involution on hard samples.

## Main results

- `dualHardSample_dualHardSample`: duality is an involution.
- `xBit_dualHardSample`, `yBit_dualHardSample`, `X_dualHardSample`, `Y_dualHardSample`,
  `input_dualHardSample`, `xVector_dualHardSample`, `yVector_dualHardSample`: bits, sets and
  vectors of the dual sample are the other player's, in reversed order.
- `disjointEvent_dualHardSample`, `specialZeroZero_dualHardSample`,
  `specialX_dualHardSample`, `specialY_dualHardSample`: the disjoint event and the
  `X_T = Y_T = false` slice are invariant, and the special bits swap.
- `xBeforeSpecial_dualHardSample`, `yAfterSpecial_dualHardSample`,
  `xLeSpecial_dualHardSample`, `yGeSpecial_dualHardSample`,
  `aliceClaimConditioning_dualHardSample`, `bobClaimConditioning_dualHardSample`: the
  windowed vectors and the corrected conditionings transport along duality.
- `not_xBit_left_and_yBit_right_of_same_conditioning`, `xBit_mix`, `yBit_mix`, `X_mix`,
  `Y_mix`, `input_mix`, `xBeforeSpecial_mix`, `yAfterSpecial_mix`, `specialX_mix`,
  `specialY_mix`, `mix_mix_swap`: the projection and involution properties of `mix`.

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

/-- The dual of a hard sample: the special coordinate is reversed (`T ↦ n - 1 - T`), Alice's
and Bob's special bits are exchanged, and the disjoint pair at coordinate `i` is the swapped
pair of the original sample at the reversed coordinate. Its generated input is `(rev B, rev A)`
when the original is `(A, B)`, and it preserves the uniform law on samples (proved in
`DualityMeasurePreserving`). This is the sample side of the "symmetric argument" in the proof
of [RY20, Thm 6.13]: the 'WLOG' step leading to eq. (6.2) treats the Bob-side term by symmetry, and
here that symmetry is realised by this involution together with `dualProtocol`, so the
Alice-side results apply verbatim to the dual protocol and dual samples. Coordinates are
reversed so that Bob's window `Y_>T` becomes an Alice window `X_<rev T` of the dual, matching
the asymmetric conditioning `(T, X_<T, Y_>T)`. -/
def dualHardSample (ω : HardSample n) : HardSample n where
  T := Fin.rev ω.T
  xT := ω.yT
  yT := ω.xT
  other := fun i => DisjointCoordinate.swap (ω.other (Fin.rev i))

/-- Dualizing a hard sample twice recovers the original sample: `dualHardSample` is an
involution. -/
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

/-- Shared engine for the windowed-vector duality lemmas: Alice's bits in the dual sample, cut
by a comparison `P` against the dual special coordinate, are the reversal of Bob's original
bits cut by a comparison `Q` against the original special coordinate, whenever the two cuts
correspond under `Fin.rev`. -/
private theorem xWindow_dualHardSample_eq_reverse (ω : HardSample n)
    (P Q : Fin n → Fin n → Prop) [DecidableRel P] [DecidableRel Q]
    (hPQ : ∀ i, P i (Fin.rev ω.T) ↔ Q ω.T (Fin.rev i)) :
    (fun i => if P i (Fin.rev ω.T) then xBit n (dualHardSample n ω) i else false) =
      reverseBoolVector n (fun i => if Q ω.T i then yBit n ω i else false) := by
  funext i
  simp only [reverseBoolVector, Function.comp_apply, xBit_dualHardSample]
  by_cases h : P i (Fin.rev ω.T)
  · have h' : Q ω.T (Fin.rev i) := (hPQ i).1 h
    rw [if_pos h, if_pos h']
  · have h' : ¬Q ω.T (Fin.rev i) := fun h' => h ((hPQ i).2 h')
    rw [if_neg h, if_neg h']

/-- Alice's before-special vector `X_<T` of the dual sample is Bob's after-special vector
`Y_>T` of the original sample in reverse order. It is a one-line instantiation of the shared
engine `xWindow_dualHardSample_eq_reverse` at the strict comparison, the cuts being matched by
`Fin.lt_rev_iff`. -/
theorem xBeforeSpecial_dualHardSample (ω : HardSample n) :
    xBeforeSpecial n (dualHardSample n ω) =
      reverseBoolVector n (yAfterSpecial n ω) := by
  -- Step 1: the `<` cut of the shared engine, with the cuts matched by `Fin.lt_rev_iff`.
  exact xWindow_dualHardSample_eq_reverse n ω (· < ·) (· < ·) fun _ => Fin.lt_rev_iff

/-- Bob's after-special vector `Y_>T` of the dual sample is Alice's before-special vector
`X_<T` of the original sample in reverse order. Obtained from `xBeforeSpecial_dualHardSample`
applied to the dual sample, using that duality and reversal are involutions. -/
theorem yAfterSpecial_dualHardSample (ω : HardSample n) :
    yAfterSpecial n (dualHardSample n ω) =
      reverseBoolVector n (xBeforeSpecial n ω) := by
  have h := xBeforeSpecial_dualHardSample n (dualHardSample n ω)
  have hdual := congrArg (reverseBoolVector n) h
  simpa [dualHardSample_dualHardSample,
    reverseBoolVector_reverseBoolVector] using hdual.symm

/-- Alice's `X_≤T` vector of the dual sample is Bob's `Y_≥T` vector of the original sample in
reverse order. It is a one-line instantiation of the shared engine
`xWindow_dualHardSample_eq_reverse` at the non-strict comparison, the cuts being matched by
`Fin.le_rev_iff`. -/
theorem xLeSpecial_dualHardSample (ω : HardSample n) :
    xLeSpecial n (dualHardSample n ω) =
      reverseBoolVector n (yGeSpecial n ω) := by
  -- Step 1: the `≤` cut of the shared engine, with the cuts matched by `Fin.le_rev_iff`.
  exact xWindow_dualHardSample_eq_reverse n ω (· ≤ ·) (· ≤ ·) fun _ => Fin.le_rev_iff

/-- Bob's `Y_≥T` vector of the dual sample is Alice's `X_≤T` vector of the original sample in
reverse order. Obtained from `xLeSpecial_dualHardSample` applied to the dual sample, using
that duality and reversal are involutions. -/
theorem yGeSpecial_dualHardSample (ω : HardSample n) :
    yGeSpecial n (dualHardSample n ω) =
      reverseBoolVector n (xLeSpecial n ω) := by
  have h := xLeSpecial_dualHardSample n (dualHardSample n ω)
  have hdual := congrArg (reverseBoolVector n) h
  simpa [dualHardSample_dualHardSample,
    reverseBoolVector_reverseBoolVector] using hdual.symm

/-- Alice's corrected conditioning `(T, X_<T, Y_≥T)` of the dual sample is the recoding
(`dualConditioningValue`: reverse `T`, swap and reverse the two vectors) of Bob's corrected
conditioning `(T, X_≤T, Y_>T)` of the original sample. -/
theorem aliceClaimConditioning_dualHardSample (ω : HardSample n) :
    aliceClaimConditioning n (dualHardSample n ω) =
      dualConditioningValue n (bobClaimConditioning n ω) := by
  rw [aliceClaimConditioning, bobClaimConditioning, dualConditioningValue,
    xBeforeSpecial_dualHardSample, yGeSpecial_dualHardSample]
  simp [specialCoordinate, dualHardSample]

/-- Bob's corrected conditioning `(T, X_≤T, Y_>T)` of the dual sample is the recoding
(`dualConditioningValue`) of Alice's corrected conditioning `(T, X_<T, Y_≥T)` of the original
sample. -/
theorem bobClaimConditioning_dualHardSample (ω : HardSample n) :
    bobClaimConditioning n (dualHardSample n ω) =
      dualConditioningValue n (aliceClaimConditioning n ω) := by
  rw [bobClaimConditioning, aliceClaimConditioning, dualConditioningValue,
    xLeSpecial_dualHardSample, yAfterSpecial_dualHardSample]
  simp [specialCoordinate, dualHardSample]

/-- If two samples agree on the conditioning data `(T, X_<T, Y_>T)`, then at every coordinate
other than `T`, Alice's bit from the first sample and Bob's bit from the second sample are not
both `true`. This is what makes `mix` well defined: before `T` the two samples share Alice's
bit, after `T` they share Bob's bit, and within a single sample the bits are disjoint
(`not_xBit_and_yBit_of_ne_special`).

**Proof sketch.** Suppose both bits are `true`; since `i ≠ T`, either `i < T` or `T < i`.
(1) If `i < T` (equivalently `i < ωY.T`, the special coordinates being equal), agreement of
`X_<T` gives that Alice's bit of `ωY` at `i` equals Alice's bit of `ωX` at `i`, so both bits
of `ωY` at `i` are `true`, contradicting disjointness within `ωY`. (2) If `T < i`, agreement
of `Y_>T` gives that Bob's bit of `ωX` at `i` equals Bob's bit of `ωY` at `i`, so both bits of
`ωX` at `i` are `true`, contradicting disjointness within `ωX`. -/
theorem not_xBit_left_and_yBit_right_of_same_conditioning
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY)
    {i : Fin n} (hi : i ≠ ωX.T) :
    ¬(xBit n ωX i = true ∧ yBit n ωY i = true) := by
  intro hbits
  by_cases hlt : i < ωX.T
  · -- Step 1: `i < T`, so Alice's bits agree and `ωY` would have both bits set
    have hltY : i < ωY.T := by
      simpa [← hT] using hlt
    have hx_eq : xBit n ωY i = xBit n ωX i := by
      have hfun := congrFun hBefore i
      simpa [xBeforeSpecial, hlt, hltY] using hfun.symm
    exact not_xBit_and_yBit_of_ne_special n ωY (by simpa [← hT] using hi)
      ⟨hx_eq.trans hbits.1, hbits.2⟩
  · -- Step 2: `T < i`, so Bob's bits agree and `ωX` would have both bits set
    have hgt : ωX.T < i := lt_of_le_of_ne (le_of_not_gt hlt) hi.symm
    have hgtY : ωY.T < i := by
      simpa [← hT] using hgt
    have hy_eq : yBit n ωX i = yBit n ωY i := by
      have hfun := congrFun hAfter i
      simpa [yAfterSpecial, hgt, hgtY] using hfun
    exact not_xBit_and_yBit_of_ne_special n ωX hi
      ⟨hbits.1, hy_eq.trans hbits.2⟩

/-- When the two samples agree on `(T, X_<T, Y_>T)`, the mixed sample has Alice's input bit
from the first sample at every coordinate. -/
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

/-- When the two samples agree on `(T, X_<T, Y_>T)`, the mixed sample has Bob's input bit from
the second sample at every coordinate. -/
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

/-- When the two samples agree on `(T, X_<T, Y_>T)`, Alice's input set of the mixed sample is
Alice's input set of the first sample. -/
theorem X_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    X n (mix n ωX ωY) = X n ωX := by
  ext i
  simp [X, xBit_mix n hT hBefore hAfter i]

/-- When the two samples agree on `(T, X_<T, Y_>T)`, Bob's input set of the mixed sample is
Bob's input set of the second sample. -/
theorem Y_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    Y n (mix n ωX ωY) = Y n ωY := by
  ext i
  simp [Y, yBit_mix n hT hBefore hAfter i]

/-- When the two samples agree on `(T, X_<T, Y_>T)`, the generated input of the mixed sample is
the pair (Alice's set of the first sample, Bob's set of the second sample): `mix` realises the
"mix-and-match" input of the rectangle in the proof of [RY20, Claim 6.14]. -/
theorem input_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    input n (mix n ωX ωY) = (X n ωX, Y n ωY) := by
  rw [input, X_mix n hT hBefore hAfter, Y_mix n hT hBefore hAfter]

/-- When the two samples agree on `(T, X_<T, Y_>T)`, the mixed sample has the same before-`T`
Alice vector `X_<T` as the first sample (hence as both). -/
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

/-- When the two samples agree on `(T, X_<T, Y_>T)`, the mixed sample has the same after-`T`
Bob vector `Y_>T` as the second sample (hence as both). -/
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

/-- Alice's special bit of the mixed sample is Alice's special bit of the first sample. -/
theorem specialX_mix (ωX ωY : HardSample n) :
    specialX n (mix n ωX ωY) = specialX n ωX := by
  simp [specialX, mix]

/-- Bob's special bit of the mixed sample is Bob's special bit of the second sample. -/
theorem specialY_mix (ωX ωY : HardSample n) :
    specialY n (mix n ωX ωY) = specialY n ωY := by
  simp [specialY, mix]

/-- When the two samples agree on `(T, X_<T, Y_>T)`, mixing `mix ωX ωY` with `mix ωY ωX`
recovers `ωX`. This is the involution behind the rectangle-counting argument for conditional
independence on `Z` fibres [RY20, Claim 6.14]: it exhibits the fibre as a product of an
Alice-side and a Bob-side set.

**Proof sketch.** Unfold `mix`: the special coordinate and Alice's special bit come from
`mix ωX ωY`, and Bob's special bit from `mix ωY ωX`, so all three are those of `ωX`; it remains
to compare the coordinate maps pointwise. At the special coordinate both sides give `ωX`'s
coordinate. At any other coordinate `i`, the outer mix rebuilds the coordinate from Alice's
bit of `mix ωX ωY` and Bob's bit of `mix ωY ωX` at `i`; by `xBit_mix` and `yBit_mix` (the
latter with the hypotheses reversed) these are Alice's and Bob's bits of `ωX` at `i`, and
rebuilding a coordinate from its own two bits returns it (`coordinateOfBits_xBit_yBit`). -/
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

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
