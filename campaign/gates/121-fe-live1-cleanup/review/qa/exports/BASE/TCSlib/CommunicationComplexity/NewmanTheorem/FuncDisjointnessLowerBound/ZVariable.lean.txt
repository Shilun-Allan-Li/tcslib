/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.HardSample

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Disjointness lower bound: the transcript variable Z

In the proof of the randomized lower bound for disjointness [RY20, Thm 6.13], `S` denotes the
transcript of a deterministic protocol run on Razborov's hard distribution and
`Q = (T, A_{<T}, B_{>T})` the conditioning variable; the key fact is that, conditioned on any
fixing of `(Q, S)`, the inputs `A` and `B` are independent [RY20, Claim 6.14]. This file
packages the pair `(Q, S)` as a single random variable `Z = (M, T, X_{<T}, Y_{>T})` on the
hard sample space, restricted to the values it actually attains, so that every fibre of `Z`
is nonempty and carries positive mass. It also defines the induced distribution on input
pairs and the dual protocol used for the "symmetric argument" of the proof (the `B_T` case,
which [RY20] dismisses as "WLOG" before eq. (6.2)).

## Main definitions

- `ProtocolType`, `TranscriptType`: deterministic protocols on pairs of subsets of `Fin n`
  with Boolean output, and their syntactic transcripts.
- `RawZType`, `rawZVariable`: the record `(M, T, X_{<T}, Y_{>T})` and the map sending a hard
  sample to its record.
- `ZType`, `zVariable`, `zFiber`, `zOutput`: the achievable `Z` values, the variable `Z`
  itself, its fibres, and the protocol output read off a `Z` value.
- `inputMeasure`, `inputDist`: the hard distribution on input pairs `(A, B)`, as a measure
  and as a finite probability space.
- `dualProtocol`, `dualProtocolTranscriptMap`: the Alice/Bob dual of a protocol and the
  induced map on transcripts.

## Main results

- `run_eq_zOutput_of_zVariable_eq`: the protocol's output on a sample is a function of its
  `Z` value.
- `volume_zFiber_ne_zero`: every achievable `Z` fibre has positive mass.
- `dualProtocolTranscriptMap_injective`: the transcript map induced by duality is injective.

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

/-- A deterministic protocol for disjointness on the universe `Fin n`: Alice and Bob each hold
a subset of `Fin n` and the protocol outputs a Boolean. This is the deterministic protocol whose
transcript `S` is analysed in [RY20, Ch. 6, 'Let S denote the messages (transcript)']. -/
abbrev ProtocolType : Type :=
  Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool

/-- The type of syntactic transcripts of a disjointness protocol `p`: the message sequences `S`
that a run of `p` can produce [RY20, Ch. 6, 'Let S denote the messages (transcript)']. -/
abbrev TranscriptType
    (p : ProtocolType n) : Type :=
  Deterministic.Protocol.Transcript p

/-- A raw value of the variable `Z = (M, T, X_<T, Y_>T)` for a protocol `p`: a transcript `M`
of `p`, a special coordinate `T`, and two Boolean vectors carrying Alice's bits before `T` and
Bob's bits after `T` (padded by `false` elsewhere). This is the pair `(Q, S)` of
[RY20, Ch. 6, Claim 6.14], with `Q = (T, A_{<T}, B_{>T})` and `S = M`. Not every raw record is
attained by a hard sample; `ZType` restricts to the achievable ones. -/
structure RawZType
    (p : ProtocolType n) where
  transcript : TranscriptType n p
  specialCoordinate : Fin n
  xBefore : Fin n → Bool
  yAfter : Fin n → Bool

namespace RawZType

variable {p : ProtocolType n}

/-- Two raw `Z` records are equal as soon as their transcript, special coordinate, before-vector
and after-vector agree. -/
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

/-- The map sending a hard sample to its raw `Z = (M, T, X_<T, Y_>T)` record: the transcript
of `p` on the generated input, the special coordinate, and the padded vectors `X_<T`, `Y_>T`.
Its fibres are the coarse special-coordinate fibres used throughout the lower bound. -/
noncomputable def rawZVariable
    (p : ProtocolType n)
    (ω : HardSample n) : RawZType n p :=
  { transcript := p.transcript (input n ω)
    specialCoordinate := specialCoordinate n ω
    xBefore := xBeforeSpecial n ω
    yAfter := yAfterSpecial n ω }

/-- The type of achievable values of `Z = (M, T, X_<T, Y_>T)` for a protocol `p`: the raw
records that are the `Z` record of at least one hard sample. Restricting to achievable values
guarantees that every fibre of `Z` is nonempty, which is what conditioning on a fixing of
`(Q, S)` in [RY20, Ch. 6, Claim 6.14] requires. -/
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

/-- Every value of `ZType` is attained: for each achievable `Z` value there is a hard sample
whose raw `Z` record is its underlying raw value. -/
theorem achievable
    (z : ZType n p) :
    ∃ ω : HardSample n, rawZVariable n p ω = z.raw :=
  z.2

/-- Two achievable `Z` values are equal as soon as their transcript, special coordinate,
before-vector and after-vector agree. -/
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

/-- The random variable `Z = (M, T, X_<T, Y_>T)` on the hard sample space, valued in achievable
records: it records the transcript of `p` on the generated input together with the conditioning
data `Q = (T, X_<T, Y_>T)`. This is the pair `(Q, S)` of [RY20, Ch. 6, Claim 6.14], packaged
as one variable and restricted to the values it attains. -/
noncomputable def zVariable
    (p : ProtocolType n)
    (ω : HardSample n) : ZType n p :=
  ⟨rawZVariable n p ω, ⟨ω, rfl⟩⟩

/-- The fibre of `Z = (M, T, X_<T, Y_>T)` above a value `z`: the set of hard samples whose
`Z` value is `z`. Fixing `(Q, S)` in [RY20, Ch. 6, Claim 6.14] means conditioning on this
event. -/
def zFiber
    (p : ProtocolType n)
    (z : ZType n p) : Set (HardSample n) :=
  (zVariable n p) ⁻¹' {z}

/-- The protocol output determined by a `Z` value: the output at the leaf of its transcript. -/
noncomputable def zOutput
    (p : ProtocolType n)
    (z : ZType n p) : Bool :=
  Deterministic.Protocol.Transcript.output z.transcript

/-- If a hard sample has `Z` value `z`, then the output of the protocol on the sample's
generated input pair `(X, Y)` is the output read off the transcript stored in `z`. In
particular the protocol's answer is a function of `Z`. -/
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
/-- Every achievable `Z` fibre has positive mass under the uniform hard-sample distribution:
it contains the witnessing sample, and the uniform measure gives each sample mass
`1 / |HardSample n| > 0`.

**Proof sketch.** The achievability witness of `z` is a sample `ω` whose `Z`-value is `z`.
Reduce to nonvanishing of the real mass, unfold the fibre as the preimage of `{z}` under the
uniform measure, and rewrite that mass as the ratio of the fibre's cardinality to that of
`HardSample n` (`uniformOn_univ_measureReal_eq_card_subtype`). Both cardinalities are
positive: the fibre contains `ω`, and the sample space is nonempty. -/
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

/-- The law of the generated input pair `(A, B)` under a uniform hard sample: the pushforward
of the uniform measure on `HardSample n` along `input`. This is Razborov's hard distribution
of [RY20, Ch. 6, 'Hard distribution'] (pairs intersect in at most the coordinate `T`, and do
so with probability `1/4`). -/
noncomputable def inputMeasure :
    Measure (Set (Fin n) × Set (Fin n)) :=
  Measure.map (input n) volume

noncomputable instance inputMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (inputMeasure n) := by
  rw [inputMeasure]
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable (f := input n))

/-- The hard distribution on input pairs `(A, B)` [RY20, Ch. 6, 'Hard distribution'], packaged
as a `FiniteProbabilitySpace`, which is the form in which the distributional error of a
protocol is defined. -/
noncomputable def inputDist :
    FiniteProbabilitySpace (Set (Fin n) × Set (Fin n)) :=
  FiniteProbabilitySpace.ofMeasure
    (Set (Fin n) × Set (Fin n)) (inputMeasure n)

/-- The dual of a protocol `p`: Alice's and Bob's roles are swapped and both input sets are
read in reversed coordinate order, so that the dual protocol on `(rev B, rev A)` behaves as `p`
on `(A, B)`. This makes explicit the "symmetric argument" of the proof of
[RY20, Thm 6.13]: the 'WLOG' step leading to eq. (6.2) assumes that the Alice-side term is the
large one and treats the Bob-side case by symmetry. Here the Bob-side case is obtained by
applying the Alice-side results to `dualProtocol p` (with samples transported by
`dualHardSample`) rather than by repeating the proof. Coordinates are reversed, not merely
swapped, because the conditioning `(A_<T, B_>T)` is not invariant under a plain swap:
reversal turns Bob's "after `T`" window into a "before `rev T`" window. -/
def dualProtocol
    (p : ProtocolType n) :
    ProtocolType n :=
  p.swap.comap (reverseSet n) (reverseSet n)

/-- The map on transcripts induced by protocol duality: a transcript of `p` becomes a transcript
of `dualProtocol p` by swapping the speaker roles and transporting along the coordinate
reversal. -/
def dualProtocolTranscriptMap
    (p : ProtocolType n) :
    TranscriptType n p → TranscriptType n (dualProtocol n p) :=
  fun transcript =>
    Deterministic.Protocol.transcriptComap p.swap (reverseSet n) (reverseSet n)
      (Deterministic.Protocol.transcriptSwap transcript)

/-- The map on transcripts induced by protocol duality is injective: distinct transcripts of `p`
have distinct duals. It is the composite of two injective transports. -/
theorem dualProtocolTranscriptMap_injective
    (p : ProtocolType n) :
    Function.Injective (dualProtocolTranscriptMap n p) := by
  exact
    (Deterministic.Protocol.transcriptComap_injective p.swap (reverseSet n) (reverseSet n)).comp
      (Deterministic.Protocol.transcriptSwap_injective p)

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
