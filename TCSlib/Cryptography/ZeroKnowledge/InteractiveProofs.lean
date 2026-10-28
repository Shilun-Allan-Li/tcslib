/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.ClassNP.PClosure
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Interactive proof systems

The definitions of [PS10, §4.5] on top of the interaction model of `Interaction.lean`
(foundation decision D8): interactive proofs with negligible soundness error
[PS10, Definition 116.1], proofs with a stated soundness error `s(|x|)` [PS10, §4.5,
constant-error proofs], witness relations [PS10, Appendix B, Definition 191.11], and
interactive proofs with an efficient prover [PS10, Definition 119.5]. The sanity theorem
`npProtocol_interactiveProof` shows the definitions are satisfiable: the one-message protocol
in which the prover sends a witness (read by the verifier up to the relation's witness-length
bound) is an interactive proof with efficient prover for every polynomially decidable witness
relation, and `WitnessRelation.mem_IP`, `NP_subset_IP` place such languages in the class `IP`
([PS10, §4.5, the remark `NP ⊆ IP`]).

**Deviation (D8):** soundness is the literal `1 - ε(|x|) < Pr[out_V = 0]` with `out_V = 0`
read as the output string `[false]`, the negligible `ε` quantified before the instance, the
cheating prover and its auxiliary input; cheating provers are arbitrary strategies with a
polynomial random tape (unbounded computation; polynomial coin tapes lose nothing by
averaging, `Protocol.exists_proverCoins_le`). Completeness is `uprob = 1`, i.e. acceptance on
every pair of random tapes. The verifier's efficiency is `Strategy.Efficient`, polynomial time
in `|x| + |z| + |messages|` (D8), so `InteractiveProof` alone does not bound the verifier's
work in `|x|` against an unbounded prover sending long messages; the class `IP` adds the
message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1).

## Main definitions

* `TCSlib.Cryptography.InteractiveProof` — interactive proof system [PS10, Definition 116.1]
  (Def-116.1); `TCSlib.Cryptography.InteractiveProofErr` — with soundness error `s` (Def-117.a);
  `TCSlib.Cryptography.IP` — the class of languages with an interactive proof whose verifier
  reads a polynomial prefix of each message (Def-117.b).
* `TCSlib.Cryptography.WitnessRelation` — a witness relation for a language
  [PS10, Definition 191.11] (Def-191.11); `TCSlib.Cryptography.witnessLanguage`,
  `TCSlib.Cryptography.witnessSet` — the language `{x | ∃ y, R x y}` and the set `R_L(x)`.
* `TCSlib.Cryptography.EfficientProverProof`,
  `TCSlib.Cryptography.EfficientProverProofErr` — interactive proofs with efficient prover
  [PS10, Definition 119.5] (Def-119.5).
* `TCSlib.Cryptography.npProtocol` — the one-message protocol in which the prover sends a
  witness, read by the verifier up to a polynomial length bound.

## Main results

* `TCSlib.Cryptography.InteractiveProofErr.interactiveProof`,
  `TCSlib.Cryptography.InteractiveProof.exists_err` — a negligible soundness error gives an
  interactive proof and conversely.
* `TCSlib.Cryptography.InteractiveProof.exists_uprob_accept_lt` — the acceptance form of
  soundness, `Pr[out_V = [true]] < ε(|x|)`.
* `TCSlib.Cryptography.WitnessRelation.mem_NP`,
  `TCSlib.Cryptography.exists_witnessRelation_of_mem_NP` — witness relations characterize
  `Complexity.NP` (the bridge to the certificate definition of `ClassNP/NP.lean`).
* `TCSlib.Cryptography.npProtocol_interactiveProof` — non-vacuity: sending a witness is an
  interactive proof with efficient prover; `TCSlib.Cryptography.npProtocol_readsPrefix`,
  `TCSlib.Cryptography.WitnessRelation.mem_IP`, `TCSlib.Cryptography.NP_subset_IP` — its
  verifier reads a polynomial prefix, hence `NP ⊆ IP` (Claim-117.c).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 116–120; Appendix B, Definition 191.11.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Definition 2.1, NP via certificates; Chapter 8.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Interactive proofs -/

/-- An interactive proof system for `L` [PS10, Definition 116.1] (Def-116.1): the verifier is
efficient; completeness — for every `x ∈ L` there is an auxiliary input `y` such that for every
`z` the honest execution `P(x, y) ↔ V(x, z)` makes `V` output `1` with probability one;
soundness — there is a negligible `ε` such that for every `x ∉ L`, every (unbounded) prover
strategy `P'` and every `z`, `V` outputs `0` in `P'(x) ↔ V(x, z)` with probability greater than
`1 - ε(|x|)`.

**Deviation (D8):** `out_V = 0` is the literal output string `[false]` on the complete
history of the fixed-alternation execution; `P'` ranges over strategies with polynomial
random tapes and receives no auxiliary input (the text's `P*(x)`); completeness is `uprob = 1`
(every pair of random tapes). The verifier is `Strategy.Efficient`, i.e. polynomial-time in
`|x| + |z| + |messages|` (D8), so this predicate alone does not bound the verifier's work in
`|x|` against an unbounded prover sending long messages; the class `IP` adds the
message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1). -/
structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
  /-- The verifier is a PPT strategy. -/
  efficientV : π.V.Efficient
  /-- Completeness: some auxiliary input makes the honest verifier accept with probability one. -/
  complete : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  /-- Soundness: against every prover strategy the verifier rejects with probability
  `> 1 - ε(|x|)` for a negligible `ε`. -/
  sound : ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])

/-- An interactive proof system with soundness error `s` [PS10, §4.5, after Definition 116.1]
(Def-117.a): as `InteractiveProof` with `1 - s(|x|) ≤ Pr[out_V = [false]]` for the given
function `s` (for instance the constant `1/2` of the single-iteration graph-isomorphism
protocol).

**Deviation (D8):** as for `InteractiveProof` (literal `[false]`, provers with polynomial
tapes, `uprob = 1` completeness; verifier time in the total input length — the message-prefix
cap is added in `IP`, run-3 audit P9-1). -/
structure InteractiveProofErr (π : Protocol) (L : Language Bool) (s : ℕ → ℝ) : Prop where
  /-- The verifier is a PPT strategy. -/
  efficientV : π.V.Efficient
  /-- Completeness: some auxiliary input makes the honest verifier accept with probability one. -/
  complete : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  /-- Soundness error `s`: the verifier rejects with probability at least `1 - s(|x|)`. -/
  sound : ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - s x.length ≤ uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])

/-- The class `IP` of languages with an interactive proof system [PS10, §4.5] (Def-117.b):
`L ∈ IP` iff some protocol `π` is an interactive proof for `L` whose verifier reads only a
polynomial prefix `m(|x|)` of each received message (`Strategy.ReadsPrefix`), as a verifier of
time complexity `t(|x|)` in the sense of the text necessarily does.

**Repair (run-3 audit P9-1):** the run-2 definition `∃ π, InteractiveProof π L` contained every
language `{x | ∃ y, T ⟨x, y⟩ = true}` with `T` polynomial-time on the pair and no bound on
`|y|` (all of RE, by computation-history checkers): under D8 the verifier's time is polynomial
in the total input including the messages, so an unbounded prover could hand it an arbitrarily
long certificate. With the cap the verifier's work is polynomial in `|x| + |z|`, as in the
text; `WitnessRelation.mem_IP` recovers `NP ⊆ IP`. -/
def IP : Set (Language Bool) :=
  {L | ∃ (π : Protocol) (m : PolyExpr), π.V.ReadsPrefix m ∧ InteractiveProof π L}

/-- A negligible soundness error gives an interactive proof: the strict clause holds with the
negligible function `ε n := s n + 2⁻¹ ^ n`. -/
theorem InteractiveProofErr.interactiveProof {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
    (hs : Negligible s) (h : InteractiveProofErr π L s) : InteractiveProof π L where
  efficientV := h.efficientV
  complete := h.complete
  sound := by
    refine ⟨fun n => s n + (2 : ℝ)⁻¹ ^ n, hs.add negligible_two_pow_neg, fun x hx P' z => ?_⟩
    have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ x.length := by positivity
    linarith [h.sound x hx P' z]

/-- An interactive proof has a negligible soundness error. -/
theorem InteractiveProof.exists_err {π : Protocol} {L : Language Bool}
    (h : InteractiveProof π L) : ∃ ε : ℕ → ℝ, Negligible ε ∧ InteractiveProofErr π L ε := by
  obtain ⟨ε, hε, hsound⟩ := h.sound
  exact ⟨ε, hε, h.efficientV, h.complete, fun x hx P' z => (hsound x hx P' z).le⟩

/-- Soundness in the acceptance form: for `x ∉ L` the verifier accepts (outputs `[true]`) with
probability less than `ε(|x|)` (the form the inventory records as equivalent; the event
`out_V = [true]` is contained in `out_V ≠ [false]`). -/
theorem InteractiveProof.exists_uprob_accept_lt {π : Protocol} {L : Language Bool}
    (h : InteractiveProof π L) : ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
        uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) < ε x.length := by
  obtain ⟨ε, hε, hsound⟩ := h.sound
  refine ⟨ε, hε, fun x hx P' z => ?_⟩
  have h1 := hsound x hx P' z
  have h2 : uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) ≤
      uprob (fun r : π.ExecCoins P' x => ¬ π.outV P' x [] z r = [false]) :=
    uprob_mono fun r hr => by simp [hr]
  rw [uprob_not] at h2
  linarith

/-! ### Witness relations -/

/-- A witness relation for `L` [PS10, Appendix B, Definition 191.11] (Def-191.11): `x ∈ L` iff
some `y` satisfies `R x y`; witnesses have polynomially bounded length; and the relation is
decidable in polynomial time on the pair `⟨x, y⟩`.

**Deviation:** the text's `R_L(x) = {y : (x, y) ∈ L}` is a typo for `∈ R_L`; the witness-length
bound is an explicit `PolyExpr` and the decider a polynomial-time string function
(`PolyTimeComputable`). -/
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where
  /-- `x ∈ L` iff `x` has a witness. -/
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  /-- Witnesses have length bounded by a polynomial in `|x|`. -/
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  /-- The relation is decidable in polynomial time on `⟨x, y⟩`. -/
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧
    ∀ x y, T (pairEncode x y) = true ↔ R x y

/-- The language of a relation, `{x | ∃ y, R x y}` [PS10, Definition 191.11]. -/
def witnessLanguage (R : List Bool → List Bool → Prop) : Language Bool := {x | ∃ y, R x y}

/-- The witness set `R_L(x) = {y | R x y}` [PS10, Definition 191.11]. -/
def witnessSet (R : List Bool → List Bool → Prop) (x : List Bool) : Set (List Bool) := {y | R x y}

/-- Membership in `witnessLanguage R` unfolds to the existence of a witness. -/
@[simp] theorem mem_witnessLanguage (R : List Bool → List Bool → Prop) (x : List Bool) :
    x ∈ witnessLanguage R ↔ ∃ y, R x y := Iff.rfl

/-- Membership in `witnessSet R x` unfolds to `R x y`. -/
@[simp] theorem mem_witnessSet (R : List Bool → List Bool → Prop) (x y : List Bool) :
    y ∈ witnessSet R x ↔ R x y := Iff.rfl

/-- A witness relation for `L` determines `L` as `witnessLanguage R`. -/
theorem WitnessRelation.eq_witnessLanguage {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L = witnessLanguage R :=
  Set.ext fun x => h.mem_iff x

/-- A language with a witness relation is in `NP` [PS10, Definition 191.11, the "iff" with
[AB09, Definition 2.1]].

**Proof sketch.** Use `Complexity.mem_NP_iff_exists_length_le` (the `pairEncode x u ∈ V`,
`|u| ≤ C(|x|+1)^c` form). From `h.bounded` take `p` and `C, c` with `p.eval n ≤ C(n+1)^c`
(`PolyExpr.eval_le`). From `h.decidable` take `T`; the verifier language is
`V := {z | T z = true}`, in `P` by `Complexity.mem_P_iff_polyTimeComputable` since
`[MultiTapeTM.indicator V z] = [T z]` (`funext`, `Bool.decide_eq_true`). The equivalence
`x ∈ L ↔ ∃ u, |u| ≤ C(|x|+1)^c ∧ pairEncode x u ∈ V` is `h.mem_iff`, the length bound and
the decider's specification. -/
theorem WitnessRelation.mem_NP {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L ∈ NP := by
  rw [mem_NP_iff_exists_length_le]
  obtain ⟨p, hp⟩ := h.bounded
  obtain ⟨C, c, hCc⟩ := p.eval_le
  obtain ⟨T, hT, hTR⟩ := h.decidable
  refine ⟨C, c, {z | T z = true}, mem_P_of_test hT, fun x => ?_⟩
  rw [h.mem_iff x]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (hp x y hy).trans (hCc _), (hTR x y).2 hy⟩
  · rintro ⟨u, -, hu⟩
    exact ⟨u, (hTR x u).1 hu⟩

/-- Every `NP` language has a witness relation [PS10, Definition 191.11, converse direction].

**Proof sketch.** From `Complexity.mem_NP_iff_exists_length_le` take `C, c, V`; set
`R x y := y.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x y ∈ V`. `mem_iff` is the
characterization; `bounded` is `PolyExpr.normal C c` (`PolyExpr.eval_normal`); `decidable`:
`T z := decide ((pairSndD z).length ≤ C * ((pairFstD z).length + 1) ^ c) && indicator V z`,
polynomial-time by `Complexity.polyTimeComputable_and`, `polyTimeComputable_lenLe` composed
with `pairEncode (unaryPoly (normal C c) ∘ pairFstD) pairSndD`, and
`mem_P_iff_polyTimeComputable`; on `pairEncode x y` the projections are `x` and `y`
(`pairFstD_pairEncode`, `pairSndD_pairEncode`). -/
theorem exists_witnessRelation_of_mem_NP {L : Language Bool} (h : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R := by
  obtain ⟨C, c, V, hV, hL⟩ := mem_NP_iff_exists_length_le.1 h
  refine ⟨fun x y => y.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x y ∈ V, hL, ?_, ?_⟩
  · exact ⟨PolyExpr.normal C c, fun x y hy => by rw [PolyExpr.eval_normal]; exact hy.1⟩
  · refine ⟨fun z => decide ((pairSndD z).length ≤ C * ((pairFstD z).length + 1) ^ c) &&
      MultiTapeTM.indicator V z, ?_, ?_⟩
    · refine polyTimeComputable_and ?_ (test_of_mem_P hV)
      have hlen := polyTimeComputable_lenLe.comp
        (((polyTimeComputable_unaryPoly (PolyExpr.normal C c)).comp
          polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)
      convert hlen using 1
      funext z
      simp [PolyExpr.eval_normal]
    · intro x y
      simp [MultiTapeTM.indicator]

/-! ### Efficient provers -/

/-- An interactive proof for `L` with efficient prover with respect to the witness relation
`R` [PS10, Definition 119.5] (Def-119.5): an interactive proof whose prover is a PPT strategy
(the witness is its auxiliary input) and which is complete for **every** witness `y` of `x`
(Definition 116.1 only asks for some auxiliary input). -/
structure EfficientProverProof (π : Protocol) (L : Language Bool)
    (R : List Bool → List Bool → Prop) : Prop extends InteractiveProof π L where
  /-- The prover is a PPT strategy. -/
  efficientP : π.P.Efficient
  /-- Completeness for every witness. -/
  completeWitness : ∀ x y, R x y → ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1

/-- An interactive proof with soundness error `s` and efficient prover with respect to `R`
[PS10, Definition 119.5 with the soundness error of §4.5] (Def-119.5, Def-117.a). -/
structure EfficientProverProofErr (π : Protocol) (L : Language Bool)
    (R : List Bool → List Bool → Prop) (s : ℕ → ℝ) : Prop extends InteractiveProofErr π L s where
  /-- The prover is a PPT strategy. -/
  efficientP : π.P.Efficient
  /-- Completeness for every witness. -/
  completeWitness : ∀ x y, R x y → ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1

/-- A negligible soundness error gives an interactive proof with efficient prover. -/
theorem EfficientProverProofErr.efficientProverProof {π : Protocol} {L : Language Bool}
    {R : List Bool → List Bool → Prop} {s : ℕ → ℝ} (hs : Negligible s)
    (h : EfficientProverProofErr π L R s) : EfficientProverProof π L R where
  toInteractiveProof := h.toInteractiveProofErr.interactiveProof hs
  efficientP := h.efficientP
  completeWitness := h.completeWitness

/-- An interactive proof with efficient prover has a negligible soundness error. -/
theorem EfficientProverProof.exists_err {π : Protocol} {L : Language Bool}
    {R : List Bool → List Bool → Prop} (h : EfficientProverProof π L R) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ EfficientProverProofErr π L R ε := by
  obtain ⟨ε, hε, herr⟩ := h.toInteractiveProof.exists_err
  exact ⟨ε, hε, herr, h.efficientP, h.completeWitness⟩

/-! ### The trivial NP protocol -/

/-- The one-message protocol in which the prover sends its auxiliary input `y` and the
verifier accepts iff `T ⟨x, y'⟩`, where `y'` is the received message truncated to its first
`p(|x|)` bits [PS10, §4.5, "`NP ⊆ IP`": the certificate is sent in one round, and a
polynomial-time verifier reads at most polynomially many bits of it]: prover first, one
message, no coins.

**Repair (run-3 audit P9-1):** the witness-length bound `p : PolyExpr` is a parameter and the
verifier reads only the first `p(|x|)` bits of the message (`npProtocol_readsPrefix`), so that
the protocol witnesses `L ∈ IP` under the repaired class; the run-2 verifier read the whole
message. -/
def npProtocol (T : List Bool → Bool) (p : PolyExpr) : Protocol where
  P := ⟨fun _ y _ _ => y, .const 0⟩
  V := ⟨fun x _ _ hist => [T (pairEncode x ((hist.headD []).take (p.eval x.length)))], .const 0⟩
  rounds := .const 1
  verifierFirst := false

/-- In `npProtocol T p` the verifier's output against any prover `P'` is the verdict `T` on
`⟨x, m'⟩`, where `m'` is the first `p(|x|)` bits of the single message `P'` sends on the empty
history. -/
theorem npProtocol_outV (T : List Bool → Bool) (p : PolyExpr) (P' : Strategy) (x y z : List Bool)
    (r : (npProtocol T p).ExecCoins P' x) :
    (npProtocol T p).outV P' x y z r =
      [T (pairEncode x ((P'.next x y (List.ofFn r.1) []).take (p.eval x.length)))] := by
  simp [Protocol.outV, Protocol.transcriptWith, npProtocol, exec, moverIsV]

/-- The verifier of `npProtocol T p` reads only the first `p(|x|)` bits of the message
(`List.take_take`). -/
theorem npProtocol_readsPrefix (T : List Bool → Bool) (p : PolyExpr) :
    (npProtocol T p).V.ReadsPrefix p := by
  intro x z r hist
  cases hist with
  | nil => rfl
  | cons m hist => simp [npProtocol, List.take_take]

/-- The verifier of `npProtocol T p` is efficient when `T` is polynomial-time: one activation of
the uniform machine computing `w ↦ [T ⟨x, m.take (p(|x|))⟩]` from the projections of the layout
`⟨⟨⟨1^n, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩`.

**Proof sketch.** `x` and the first message `m` are fixed `pairFstD`/`pairSndD` projection
chains of the raw input `w` (`PolyTimeComputable.comp`); the truncation `m.take (p(|x|))` is
`Complexity.polyTimeComputable_pairTakePoly p` applied to `⟨x, m⟩`
(`PolyTimeComputable.pairEncode`), and `T` is applied to `⟨x, m.take (p(|x|))⟩` (`hT.comp`).
The uniform machine `NUPPT.ofPolyTimeUniform` of this function has the required next-message
function on every history (`NUPPT.runAtL_ofPolyTimeUniform`, `Strategy.pairFstD_encodeMsgs`). -/
theorem npProtocol_efficientV (T : List Bool → Bool) (p : PolyExpr)
    (hT : PolyTimeComputable fun z => [T z]) : (npProtocol T p).V.Efficient := by
  have harg : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hx : PolyTimeComputable fun w => pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp harg)
  have hm : PolyTimeComputable fun w => pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp harg)
  have htake : PolyTimeComputable fun w =>
      (pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w))))).take
        (p.eval (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w))))).length) := by
    convert (polyTimeComputable_pairTakePoly p).comp (hx.pairEncode hm) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hF : PolyTimeComputable fun w =>
      [T (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w)))))
        ((pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w))))).take
          (p.eval (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w))))).length)))] :=
    hT.comp (hx.pairEncode htake)
  refine ⟨NUPPT.ofPolyTimeUniform hF (.const 0), NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => ?_⟩
  simp [npProtocol, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput,
    Strategy.pairFstD_encodeMsgs]

/-- The prover of `npProtocol T p` is efficient: it copies the auxiliary input, the projection
`pairSndD ∘ pairFstD` of the argument of the layout. -/
theorem npProtocol_efficientP (T : List Bool → Bool) (p : PolyExpr) :
    (npProtocol T p).P.Efficient := by
  have harg : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hF : PolyTimeComputable fun w => pairSndD (pairFstD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp harg)
  refine ⟨NUPPT.ofPolyTimeUniform hF (.const 0), NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => ?_⟩
  simp [npProtocol, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput]

/-- Non-vacuity of Definitions 116.1 and 119.5 [PS10, §4.5, "`NP ⊆ IP`"]: for a witness relation
`R` of `L` decided by the polynomial-time predicate `T`, with witnesses of length at most
`p(|x|)`, the one-message protocol in which the prover sends a witness is an interactive proof
for `L` with efficient prover with respect to `R` (the verifier rejects every `x ∉ L` with
probability one).

**Repair (run-3 audit P9-1):** the witness-length bound `p` with `hp` added (the verifier of
`npProtocol T p` reads only `p(|x|)` bits).

**Proof sketch.** The verifier's output is `[T ⟨x, m.take (p(|x|))⟩]` for the message `m` sent
(`npProtocol_outV`); the honest prover sends `y`, which the truncation leaves unchanged since
`|y| ≤ p(|x|)` (`hp`, `List.take_of_length_le`). Completeness: for `x ∈ L` take a witness `y`
(`hR.mem_iff`); then `T ⟨x, y⟩ = true` (`hTR`) on every coin pair, so the probability is one
(`HardcoreBit.uprob_eq_one_of_forall`). Soundness with `ε n := 2⁻¹ ^ n`
(`negligible_two_pow_neg`; the literal clause is strict, so `ε = 0` is not admissible): for
`x ∉ L` no string — in particular no truncated message — is a witness, so `T ⟨x, ·⟩ = false`
and the verifier outputs `[false]` on every coin pair, with probability `1 > 1 - ε(|x|)`.
Efficiency of both parties: `npProtocol_efficientV`, `npProtocol_efficientP`. -/
theorem npProtocol_interactiveProof {L : Language Bool} {R : List Bool → List Bool → Prop}
    (hR : WitnessRelation L R) (T : List Bool → Bool) (p : PolyExpr)
    (hT : PolyTimeComputable fun z => [T z])
    (hTR : ∀ x y, T (pairEncode x y) = true ↔ R x y)
    (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
    EfficientProverProof (npProtocol T p) L R where
  efficientV := npProtocol_efficientV T p hT
  complete := by
    intro x hx
    obtain ⟨y, hy⟩ := (hR.mem_iff x).1 hx
    refine ⟨y, fun z => HardcoreBit.uprob_eq_one_of_forall fun r => ?_⟩
    rw [npProtocol_outV]
    simp [npProtocol, List.take_of_length_le (hp x y hy), (hTR x y).2 hy]
  sound := by
    refine ⟨fun n => (2 : ℝ)⁻¹ ^ n, negligible_two_pow_neg, fun x hx P' z => ?_⟩
    have hall : ∀ r : (npProtocol T p).ExecCoins P' x,
        (npProtocol T p).outV P' x [] z r = [false] := by
      intro r
      rw [npProtocol_outV]
      have hno : ¬ R x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length)) :=
        fun hw => hx ((hR.mem_iff x).2 ⟨_, hw⟩)
      have hfalse :
          T (pairEncode x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length))) = false := by
        rw [← Bool.not_eq_true, hTR]
        exact hno
      rw [hfalse]
    rw [HardcoreBit.uprob_eq_one_of_forall hall]
    exact sub_lt_self _ (by positivity)
  efficientP := npProtocol_efficientP T p
  completeWitness := by
    intro x y hy z
    refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
    rw [npProtocol_outV]
    simp [npProtocol, List.take_of_length_le (hp x y hy), (hTR x y).2 hy]

/-- Every language with a witness relation is in `IP` [PS10, §4.5, "`NP ⊆ IP`"] (Claim-117.c):
the one-message protocol `npProtocol T p`, with the relation's decider `T` and witness-length
bound `p`, is an interactive proof whose verifier reads only `p(|x|)` bits of the message
(`npProtocol_readsPrefix`, `npProtocol_interactiveProof`). -/
theorem WitnessRelation.mem_IP {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L ∈ IP := by
  obtain ⟨p, hp⟩ := h.bounded
  obtain ⟨T, hT, hTR⟩ := h.decidable
  exact ⟨npProtocol T p, p, npProtocol_readsPrefix T p,
    (npProtocol_interactiveProof h T p hT hTR hp).toInteractiveProof⟩

/-- `NP ⊆ IP` [PS10, §4.5] (Claim-117.c): every `NP` language has a witness relation
(`exists_witnessRelation_of_mem_NP`), hence an interactive proof with a prefix-reading
verifier (`WitnessRelation.mem_IP`). -/
theorem NP_subset_IP : NP ⊆ IP := fun _ h =>
  (Classical.choose_spec (exists_witnessRelation_of_mem_NP h)).mem_IP

end TCSlib.Cryptography
