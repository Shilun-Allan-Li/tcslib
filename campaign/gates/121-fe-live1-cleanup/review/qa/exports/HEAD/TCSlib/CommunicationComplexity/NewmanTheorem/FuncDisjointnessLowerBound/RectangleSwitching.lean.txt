/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.ZFiberMeasure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Disjointness lower bound: rectangle switching (Claim 6.14)

The conditional independence of the special bits `X_T` and `Y_T` given a fibre of
`Z = (M, T, X_<T, Y_>T)`, that is `p(a_t b_t | q s) = p(a_t | q s) · p(b_t | q s)`
[RY20, Claim 6.14]. The textbook argument is that fixing `Q` makes `A, B` independent and
fixing the transcript `S` restricts the inputs to a rectangle, which preserves independence.
Here this is made combinatorial: two samples in the same fibre can be mixed (Alice's side from
one, Bob's side from the other) and the mix stays in the fibre, because the transcript's input
set is a rectangle; the switching map `(ωX, ωY) ↦ (mix ωX ωY, mix ωY ωX)` is then a bijection
whose cardinality identity is exactly the product formula. The file concludes with the
consequences used downstream: Alice's conditional special-bit law does not change when one
further conditions on `Y_T = 0`, the fibre KL cost can be rewritten through that conditioning,
and the pair distance `zDistance` is at most the sum of the two one-bit distances.

## Main definitions

* `goodZ`, `goodZEvent`: the `Z` values (and the samples) whose conditional special-pair law
  is within `2γ` of uniform.

## Main results

* `mixed_inputs_mem_transcript_of_zVariable_eq`, `zVariable_mix_eq_of_same_zVariable`: the
  transcript set is a rectangle, so mixing two samples of a fibre stays in the fibre.
* `card_fiber_inter_specialX_mul_card_fiber_inter_specialY`,
  `fiber_volume_factorization`: the switching bijection and its cardinality / measure form.
* `conditionalSpecialPairLaw_eq_prod`: [RY20, Claim 6.14], the conditional law of
  `(X_T, Y_T)` on a fibre is the product of its marginals.
* `conditionalSpecialXLaw_eq_cond_specialYFalse`, `xFiberKL_eq_cond_specialYFalse_klDiv`,
  `xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv_of_ne_zero`: Alice's law
  and KL cost on a fibre are unchanged by conditioning on `Y_T = 0`.
* `zDistance_le_xDistance_add_yDistance`, `mem_goodZEvent_of_xDistance_yDistance_le`: the pair
  distance is at most `α + β`, so small one-bit distances make a fibre good.

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

/-- A `Z` value is good (for threshold `γ`) when the law of `(X_T, Y_T)` conditioned on its
fibre is within total-variation distance `2γ` of the uniform law on two bits. These are the
fibres in which `p(a_t | q s)` and `p(b_t | q s)` are both close to uniform in
[RY20, Ch. 6, after Claim 6.14], with `ν₁ = ν₂ = γ`. -/
def goodZ
    (p : ProtocolType n)
    (γ : ℝ)
    (z : ZType n p) : Prop :=
  zDistance n p z ≤ 2 * γ

/-- The set of hard samples whose `Z` value is good for threshold `γ`: the good fibres of
[RY20, Ch. 6, after Claim 6.14] pulled back to the sample space through `Z`. -/
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

/-- If a sample has `Z` value `z`, its special coordinate is the special-coordinate component
of `z`. -/
theorem specialCoordinate_eq_of_zVariable_eq
    (p : ProtocolType n)
    {z : ZType n p}
    {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    specialCoordinate n ω = z.specialCoordinate := by
  simpa [zVariable, rawZVariable, ZType.specialCoordinate] using
    congrArg (fun z : ZType n p => z.specialCoordinate) hω

/-- If a sample has `Z` value `z`, its window `X_<T` of Alice's bits before the special
coordinate is the corresponding component of `z`. -/
theorem xBeforeSpecial_eq_of_zVariable_eq
    (p : ProtocolType n)
    {z : ZType n p}
    {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    xBeforeSpecial n ω = z.xBefore := by
  simpa [zVariable, rawZVariable, ZType.xBefore] using
    congrArg (fun z : ZType n p => z.xBefore) hω

/-- If a sample has `Z` value `z`, its window `Y_>T` of Bob's bits after the special
coordinate is the corresponding component of `z`. -/
theorem yAfterSpecial_eq_of_zVariable_eq
    (p : ProtocolType n)
    {z : ZType n p}
    {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    yAfterSpecial n ω = z.yAfter := by
  simpa [zVariable, rawZVariable, ZType.yAfter] using
    congrArg (fun z : ZType n p => z.yAfter) hω

/-- If two samples `ω`, `ω'` lie in the same `Z` fibre, then both mixed input pairs
`(X ω', Y ω)` and `(X ω, Y ω')` lie in the input set of the common transcript. This is the
step 'fixing `S` restricts the inputs to a rectangle' in the proof of [RY20, Claim 6.14]:
the input set of a transcript is a combinatorial rectangle. -/
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

/-- If two samples `ωX`, `ωY` lie in the same `Z` fibre, then their mix (special coordinate
and Alice's side from `ωX`, Bob's side from `ωY`) lies in that fibre as well. This is the
rectangle property 'fixing `S` restricts the inputs to a rectangle' of the proof of
[RY20, Claim 6.14], transported from input pairs to samples.

**Proof sketch.** The two samples agree on the special coordinate and on the windows `X_<T`,
`Y_>T`, so the input generated by the mix is the mixed pair `(X ωX, Y ωY)`. That pair lies
in the transcript's input set because the latter is a rectangle, hence the transcript of the
mix is the transcript component of `z`. The special coordinate and the two windows of the
mix are those of `ωX` resp. `ωY`, which are the components of `z`; the four components
together give `Z(mix) = z`. -/
theorem zVariable_mix_eq_of_same_zVariable
    (p : ProtocolType n)
    {z : ZType n p}
    {ωX ωY : HardSample n}
    (hωX : zVariable n p ωX = z)
    (hωY : zVariable n p ωY = z) :
    zVariable n p (mix n ωX ωY) = z := by
  -- Step 1: the two samples agree on `T`, `X_<T`, `Y_>T`, so the mix generates `(X ωX, Y ωY)`.
  have hT := specialCoordinate_eq_of_same_zVariable n p hωX hωY
  have hBefore := xBeforeSpecial_eq_of_same_zVariable n p hωX hωY
  have hAfter := yAfterSpecial_eq_of_same_zVariable n p hωX hωY
  have hinput := input_mix n hT hBefore hAfter
  -- Step 2: the mixed pair lies in the transcript rectangle, so the mix has transcript `z`.
  have hleaf :
      input n (mix n ωX ωY) ∈
        Deterministic.Protocol.Transcript.inputSet z.transcript := by
    have hmixed := mixed_inputs_mem_transcript_of_zVariable_eq n p hωX hωY
    simpa [hinput] using hmixed.2
  have htranscript : p.transcript (input n (mix n ωX ωY)) = z.transcript :=
    Deterministic.Protocol.transcript_eq_of_mem z.transcript hleaf
  -- Step 3: the special coordinate and the windows of the mix are the components of `z`.
  have hTz : specialCoordinate n (mix n ωX ωY) = z.specialCoordinate := by
    have hTωX := specialCoordinate_eq_of_zVariable_eq n p hωX
    simpa [specialCoordinate, mix] using hTωX
  have hBeforeZ : xBeforeSpecial n (mix n ωX ωY) = z.xBefore := by
    rw [xBeforeSpecial_mix n hT hBefore hAfter]
    exact xBeforeSpecial_eq_of_zVariable_eq n p hωX
  have hAfterZ : yAfterSpecial n (mix n ωX ωY) = z.yAfter := by
    rw [yAfterSpecial_mix n hT hBefore hAfter]
    exact yAfterSpecial_eq_of_zVariable_eq n p hωY
  -- Step 4: assemble the four components.
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
/-- For every `Z` value `z` and bit pair `b = (bX, bY)`, the number of samples in the fibre
with `X_T = bX` times the number in the fibre with `Y_T = bY` equals the number in the fibre
with `(X_T, Y_T) = b` times the size of the fibre. This is the counting form of
'fixing `S` restricts the inputs to a rectangle' in the proof of [RY20, Claim 6.14]: it is
the product formula `p(ab | qs) = p(a | qs) p(b | qs)` with all four probabilities written
as counts over the uniform fibre.

**Proof sketch.** Write `A`, `B` for the samples of the fibre with `X_T = bX`, resp.
`Y_T = bY`, and `C`, `D` for the samples of the fibre with `(X_T, Y_T) = b`, resp. the whole
fibre. The switching map `(ωX, ωY) ↦ (mix ωX ωY, mix ωY ωX)` sends `A × B` to `C × D`: the
first mix stays in the fibre and has special pair `b`, the second stays in the fibre. The map
`(ωPair, ω) ↦ (mix ωPair ω, mix ω ωPair)` sends `C × D` back to `A × B` by the same lemmas.
Both composites are the identity because mixing twice with the roles swapped recovers the
original sample when the two samples share `T`, `X_<T`, `Y_>T`. The bijection
`A × B ≃ C × D` gives the cardinality identity. -/
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
  -- The bijection `A × B ≃ C × D` given by the switching map.
  have hcard : Fintype.card (A × B) = Fintype.card (C × D) := by
    refine Fintype.card_congr
      { toFun := ?toFun
        invFun := ?invFun
        left_inv := ?left_inv
        right_inv := ?right_inv }
    -- Step 1: forward map `(ωX, ωY) ↦ (mix ωX ωY, mix ωY ωX)` lands in `C × D`.
    · intro ab
      refine
        (⟨mix n ab.1.1 ab.2.1,
            mix_mem_fiber_inter_specialPair_of_mem_specialX_specialY n p ab.1.2 ab.2.2⟩,
          ⟨mix n ab.2.1 ab.1.1,
            mix_swap_mem_fiber_of_mem_specialX_specialY n p ab.1.2 ab.2.2⟩)
    -- Step 2: inverse map `(ωPair, ω) ↦ (mix ωPair ω, mix ω ωPair)` lands in `A × B`.
    · intro cd
      refine
        (⟨mix n cd.1.1 cd.2.1,
            mix_mem_fiber_inter_specialX_of_mem_specialPair_fiber n p cd.1.2 cd.2.2⟩,
          ⟨mix n cd.2.1 cd.1.1,
            mix_mem_fiber_inter_specialY_of_mem_fiber_specialPair n p cd.2.2 cd.1.2⟩)
    -- Step 3: inverse ∘ forward is the identity, by the mix-mix-swap identity.
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
    -- Step 4: forward ∘ inverse is the identity, by the same identity.
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
  -- Step 5: the cardinality of a product is the product of cardinalities.
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

open Classical in
/-- For every `Z` value `z` and bit pair `b = (bX, bY)`, the uniform mass of the fibre times
the uniform mass of the fibre intersected with `(X_T, Y_T) = b` equals the uniform mass of
the fibre intersected with `X_T = bX` times that of the fibre intersected with `Y_T = bY`.
This is the cross-multiplied form of `p(ab | qs) = p(a | qs) p(b | qs)` from
'fixing `S` restricts the inputs to a rectangle' in the proof of [RY20, Claim 6.14], stated
for the unconditioned uniform law so that no fibre mass needs to be inverted.

**Proof sketch.** Under the uniform law the mass of a set is its cardinality divided by the
size of the sample space, so each of the four masses is such a quotient. The cardinality
identity `card_fiber_inter_specialX_mul_card_fiber_inter_specialY`, cast to the reals, is
the numerator identity; clearing the common denominator gives the claim. -/
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
  -- Step 1: each uniform mass is a cardinality divided by the size of the sample space.
  rw [measureReal_eq_card_subtype_div n F, measureReal_eq_card_subtype_div n P,
    measureReal_eq_card_subtype_div n X, measureReal_eq_card_subtype_div n Y]
  -- Step 2: the switching cardinality identity, cast to the reals.
  have hcard := card_fiber_inter_specialX_mul_card_fiber_inter_specialY n p z b
  have hcard_real :
      (Fintype.card {ω : HardSample n // ω ∈ X} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ Y} : ℝ) =
      (Fintype.card {ω : HardSample n // ω ∈ P} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ F} : ℝ) := by
    dsimp only [F, P, X, Y]
    exact_mod_cast hcard
  -- Step 3: clear the common denominator.
  have hN : (Fintype.card (HardSample n) : ℝ) ≠ 0 := by positivity
  have hcard_real' :
      (Fintype.card {ω : HardSample n // ω ∈ F} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ P} : ℝ) =
      (Fintype.card {ω : HardSample n // ω ∈ X} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ Y} : ℝ) := by
    rw [mul_comm, ← hcard_real]
  field_simp [hN]
  convert hcard_real'

/-- If, for each of the four bit pairs `b`, the conditional probability of `(X_T, Y_T) = b` on
the fibre `Z = z` is the product of the conditional probabilities of `X_T = b.1` and
`Y_T = b.2`, then the conditional law of `(X_T, Y_T)` is the product of the conditional laws
of `X_T` and `Y_T`. This is the reduction of [RY20, Claim 6.14]
(`p(ab | qs) = p(a | qs) p(b | qs)` at the special coordinate) to its pointwise form. -/
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
  -- Step 1: the singleton `{(bx, bY)}` is the rectangle `{bx} ×ˢ {bY}`, on which the product
  -- measure factors.
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul]
  rfl

/-- If, for each bit pair `b`, the probability of `(X_T, Y_T) = b` under the hard
distribution conditioned on the fibre `Z = z` is the product of the conditional probabilities
of `X_T = b.1` and `Y_T = b.2`, then the conditional law of `(X_T, Y_T)` is the product of
the conditional laws of `X_T` and `Y_T`. This is [RY20, Claim 6.14]
(`p(ab | qs) = p(a | qs) p(b | qs)` at the special coordinate) with the hypothesis phrased
on the fibre measure rather than on the pushed-forward laws. -/
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

/-- If, for each bit pair `b`, the uniform mass of the fibre `Z = z` times the uniform mass of
the fibre intersected with `(X_T, Y_T) = b` equals the product of the uniform masses of the
fibre intersected with `X_T = b.1` and with `Y_T = b.2`, then the conditional law of
`(X_T, Y_T)` on the fibre is the product of the conditional laws of `X_T` and `Y_T`. This is
[RY20, Claim 6.14] (`p(ab | qs) = p(a | qs) p(b | qs)` at the special coordinate) with the
hypothesis cross-multiplied so that it refers to the unconditioned uniform law; the
conditional probabilities are recovered by dividing by the positive fibre mass.

**Proof sketch.** Reduce via `conditionalSpecialPairLaw_eq_prod_of_zFiberMeasure_factorization`
to the factorization of the fibre measure at each bit pair `b`, then rewrite each
fibre-measure probability as a ratio of uniform masses (`zFiberMeasure_real_apply`). The fibre
has nonzero uniform mass (`volume_zFiber_ne_zero`), so clearing denominators turns the goal
into exactly the cross-multiplied hypothesis at `b`. -/
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
/-- For every `Z` value `z`, the law of the special bit pair `(X_T, Y_T)` under the hard
distribution conditioned on the fibre `Z = z` is the product of the conditional laws of
`X_T` and of `Y_T`. This is [RY20, Claim 6.14]: `p(ab | qs) = p(a | qs) p(b | qs)`, here
stated at the special coordinate only, which is all the lower bound uses. The proof is the
rectangle-switching identity `fiber_volume_factorization`. -/
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
  -- Step 1: the singleton `{(bX, bY)}` is the rectangle `{bX} ×ˢ {bY}`, on which the product
  -- measure factors.
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul]
  rfl

open Classical in
/-- If the conditional law of `(X_T, Y_T)` on the fibre `Z = z` is the product of its
marginals, and `Y_T = bY` has positive conditional probability on that fibre, then the
conditional law of `X_T` on the fibre equals the law of `X_T` under the fibre measure further
conditioned on `Y_T = bY`. This is the independence consequence of [RY20, Claim 6.14] that
lets the Alice-side quantities be computed with `B_T = 0` fixed.

**Proof sketch.** Compare the masses of each singleton `{bX}`. The right-hand side is the
conditional quotient `P(Y_T = bY ∧ X_T = bX) / P(Y_T = bY)` under the fibre measure, and the
event in the numerator is `(X_T, Y_T) = (bX, bY)`. By the product hypothesis its mass is
`P(X_T = bX) · P(Y_T = bY)`, and cancelling the nonzero factor `P(Y_T = bY)` leaves
`P(X_T = bX)`, the left-hand side. -/
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
  -- Step 1: compare singleton masses and unfold the conditioning as a quotient.
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
  -- Step 2: the numerator event is the special-pair event `(X_T, Y_T) = (bX, bY)`.
  have hpair :
      ((specialY n) ⁻¹' {bY}) ∩ ((specialX n) ⁻¹' {bX}) =
        (specialPair n) ⁻¹' {(bX, bY)} := by
    ext ω
    simp [specialPair, specialX, specialY, and_comm]
  -- Step 3: factor the pair mass by the product hypothesis and cancel `P(Y_T = bY) ≠ 0`.
  have hfactor :=
    conditionalSpecialPairLaw_singleton_factorization_of_eq_prod n p z hprod (bX, bY)
  rw [conditionalSpecialPairLaw_singleton, conditionalSpecialXLaw_singleton,
    conditionalSpecialYLaw_singleton] at hfactor
  rw [hpair, hfactor]
  field_simp [hY]

open Classical in
/-- If `Y_T = 0` has positive probability on the fibre `Z = z`, then the conditional law of
Alice's special bit on the fibre equals its law under the fibre measure further conditioned
on `Y_T = 0`: `p(a_t | q s) = p(a_t | q s, b_t = 0)`. This is the consequence of
[RY20, Claim 6.14] used to pass from `I(A_T : S | Q, B_T = 0)` to the fibre-wise Alice
quantities. -/
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
/-- For every `Z` value `z`, the total-variation distance of the conditional law of
`(X_T, Y_T)` from the uniform pair is at most the sum of the one-bit distances `α` and `β`
of its two marginals from the uniform bit. This is the step 'the disjointness probability is
within `ν₁ + ν₂` of `1/4`' of [RY20, Ch. 6, after Claim 6.14]: by [RY20, Claim 6.14] the
pair law is a product, and the total-variation distance between products is subadditive. -/
theorem zDistance_le_xDistance_add_yDistance
    (p : ProtocolType n)
    (z : ZType n p) :
    zDistance n p z ≤ xDistance n p z + yDistance n p z := by
  simpa [zDistance, xDistance, yDistance, conditionalSpecialPairLaw_eq_prod n p z,
    uniformBoolPair_eq_prod] using
    TVDistance.tvDistance_prod_le
      (conditionalSpecialXLaw n p z) uniformBool
      (conditionalSpecialYLaw n p z) uniformBool

/-- If, at the `Z` value of a sample, both one-bit distances `α` and `β` are at most `γ`,
then the sample lies in the good event for threshold `γ`, i.e. its pair law is within `2γ`
of uniform. This packages 'the disjointness probability is within `ν₁ + ν₂` of `1/4`' of
[RY20, Ch. 6, after Claim 6.14] with `ν₁ = ν₂ = γ`. -/
theorem mem_goodZEvent_of_xDistance_yDistance_le
    (p : ProtocolType n)
    {γ : ℝ} {ω : HardSample n}
    (hx : xDistance n p (zVariable n p ω) ≤ γ)
    (hy : yDistance n p (zVariable n p ω) ≤ γ) :
    ω ∈ goodZEvent n p γ := by
  have h := zDistance_le_xDistance_add_yDistance n p (zVariable n p ω)
  change zDistance n p (zVariable n p ω) ≤ 2 * γ
  linarith

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
