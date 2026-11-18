/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Simulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Correctness
import TCSlib.Cryptography.Games.Advantage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The semi-adaptive simulation experiment

Public parameters and the public key precede the adversary's challenge. Exactly
one challenge is accepted. Keys before it and later challenges return failure.
Real keys use the honest master key; ideal keys use the stored public challenge
and each allowed scalar. The simulator never receives the private challenge.

## Main definitions

* `SAChallenge`: the challenger's committed input pair.
* `FEScheme.Raw.saImpl`: the wire adapter for typed optional answers.
* `FEScheme.Raw.realSAImpl`, `idealSAImpl`: actual stateful oracle handlers.
* `FEScheme.Raw.saGame`, `saSimAdv`: the two-experiment simulation advantage.

## Main results

Handler case readers and complete experiment equations expose every branch.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; ePrint 2020/1420, §2.2, p.5.
* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, 2020, §4.1, pp.11–12.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open TCSlib.Cryptography.Pairing
open Complexity Turing TCSlib.Cryptography.Games

/-- The challenger retains the committed public/private pair to evaluate each
adaptive query's allowed scalar. [Wee20, §2.2, p.5]. -/
structure SAChallenge (C : FnClass) (kappa : ℕ) where
  /-- The public challenge input. -/
  publicInput : Fin (C.pubLen.eval kappa) → Bool
  /-- The private challenge input, hidden from the simulator. -/
  privateInput : Fin (C.privLen.eval kappa) → Bool

namespace FEScheme.Raw

variable {C : FnClass} (S : FEScheme.Raw C)

/-- The real challenger records whether its one challenge has occurred. -/
abbrev SAState (S : FEScheme.Raw C) (kappa : ℕ) : Type := Option (SAChallenge C kappa)

/-- Real state is the optional committed challenge. -/
theorem saState_eq (kappa : ℕ) : S.SAState kappa = Option (SAChallenge C kappa) := rfl

/-- The ideal challenger retains simulator state separately from its hidden input pair. -/
abbrev SAIdealState (Sim : SASimulator.Raw S) (kappa : ℕ) (pp : PublicParams S.G kappa) :
    Type := Sim.St kappa pp × S.SAState kappa

/-- Ideal state is exactly the simulator state paired with the challenger commitment. -/
theorem saIdealState_eq (Sim : SASimulator.Raw S) (kappa : ℕ)
    (pp : PublicParams S.G kappa) :
    S.SAIdealState Sim kappa pp = (Sim.St kappa pp × S.SAState kappa) := rfl

/-- Adapt typed challenge/key handlers to the library bit specification, using the
shared optional-answer encoding. Technical oracle-interface glue. -/
noncomputable def saImpl {sigma : Type} (kappa : ℕ) (pp : PublicParams S.G kappa)
    (challenge : (Fin (C.pubLen.eval kappa) → Bool) →
      (Fin (C.privLen.eval kappa) → Bool) → sigma → ProbComp (Option (S.CT kappa pp) × sigma))
    (key : (Fin (C.fnLen.eval kappa) → Bool) → sigma →
      ProbComp (Option (S.SK kappa pp) × sigma)) :
    QueryImpl (S.saSpec kappa) sigma unifSpec
  | 0, xy, st => (challenge (S.saSplitChallenge kappa xy).1
      (S.saSplitChallenge kappa xy).2 st).bind fun o =>
      .pure (S.saCTAnswer kappa pp o.1, o.2)
  | 1, f, st => (key (S.saKeyFunction kappa f) st).bind fun o =>
      .pure (S.saSKAnswer kappa pp o.1, o.2)

/-- Oracle zero calls the typed challenge handler and encodes its optional answer. -/
theorem saImpl_zero_onSpec {sigma : Type} (kappa : ℕ) (pp : PublicParams S.G kappa)
    (challenge : (Fin (C.pubLen.eval kappa) → Bool) →
      (Fin (C.privLen.eval kappa) → Bool) → sigma → ProbComp (Option (S.CT kappa pp) × sigma))
    (key : (Fin (C.fnLen.eval kappa) → Bool) → sigma →
      ProbComp (Option (S.SK kappa pp) × sigma))
    (xy : (S.saSpec kappa).dom 0) (st : sigma) :
    S.saImpl kappa pp challenge key 0 xy st =
      (challenge (S.saSplitChallenge kappa xy).1 (S.saSplitChallenge kappa xy).2 st).bind
        fun o => .pure (S.saCTAnswer kappa pp o.1, o.2) := rfl

/-- Oracle one calls the typed key handler and encodes its optional answer. -/
theorem saImpl_one_onSpec {sigma : Type} (kappa : ℕ) (pp : PublicParams S.G kappa)
    (challenge : (Fin (C.pubLen.eval kappa) → Bool) →
      (Fin (C.privLen.eval kappa) → Bool) → sigma → ProbComp (Option (S.CT kappa pp) × sigma))
    (key : (Fin (C.fnLen.eval kappa) → Bool) → sigma →
      ProbComp (Option (S.SK kappa pp) × sigma))
    (f : (S.saSpec kappa).dom 1) (st : sigma) :
    S.saImpl kappa pp challenge key 1 f st =
      (key (S.saKeyFunction kappa f) st).bind fun o =>
        .pure (S.saSKAnswer kappa pp o.1, o.2) := rfl

/-- The real challenge handler accepts the first input pair and rejects repeats.
[Wee20, §2.2, p.5]. -/
noncomputable def realSAChallenge (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (x : Fin (C.pubLen.eval kappa) → Bool)
    (y : Fin (C.privLen.eval kappa) → Bool) :
    S.SAState kappa → ProbComp (Option (S.CT kappa pp) × S.SAState kappa)
  | none => (S.enc kappa pp pk x y).bind fun ct => .pure (some ct, some ⟨x, y⟩)
  | some a => .pure (none, some a)

/-- The first real challenge produces an honest ciphertext and records its inputs. -/
theorem realSAChallenge_none (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (x : Fin (C.pubLen.eval kappa) → Bool)
    (y : Fin (C.privLen.eval kappa) → Bool) :
    S.realSAChallenge kappa pp pk x y none =
      (S.enc kappa pp pk x y).bind fun ct => .pure (some ct, some ⟨x, y⟩) := rfl

/-- A repeated real challenge fails and leaves the commitment unchanged. -/
theorem realSAChallenge_some (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (x : Fin (C.pubLen.eval kappa) → Bool)
    (y : Fin (C.privLen.eval kappa) → Bool) (a : SAChallenge C kappa) :
    S.realSAChallenge kappa pp pk x y (some a) = .pure (none, some a) := rfl

/-- The real key handler rejects calls before the challenge and otherwise samples
an honest key for the adaptive function query. [Wee20, §2.2, p.5]. -/
noncomputable def realSAKey (kappa : ℕ) (pp : PublicParams S.G kappa)
    (msk : S.MSK kappa pp) (f : Fin (C.fnLen.eval kappa) → Bool) :
    S.SAState kappa → ProbComp (Option (S.SK kappa pp) × S.SAState kappa)
  | none => .pure (none, none)
  | some a => (S.keyGen kappa pp msk f).bind fun sk => .pure (some sk, some a)

/-- A real key request before the challenge fails. -/
theorem realSAKey_none (kappa : ℕ) (pp : PublicParams S.G kappa)
    (msk : S.MSK kappa pp) (f : Fin (C.fnLen.eval kappa) → Bool) :
    S.realSAKey kappa pp msk f none = .pure (none, none) := rfl

/-- A real key request after the challenge samples its honest key. -/
theorem realSAKey_some (kappa : ℕ) (pp : PublicParams S.G kappa)
    (msk : S.MSK kappa pp) (f : Fin (C.fnLen.eval kappa) → Bool)
    (a : SAChallenge C kappa) : S.realSAKey kappa pp msk f (some a) =
    (S.keyGen kappa pp msk f).bind fun sk => .pure (some sk, some a) := rfl

/-- The ideal challenge handler sends only x to the simulator and keeps y in
challenger state for future scalar evaluations. [Wee20, §2.2, p.5]. -/
noncomputable def idealSAChallenge (Sim : SASimulator.Raw S) (kappa : ℕ)
    (pp : PublicParams S.G kappa) (x : Fin (C.pubLen.eval kappa) → Bool)
    (y : Fin (C.privLen.eval kappa) → Bool) :
    S.SAIdealState Sim kappa pp →
      ProbComp (Option (S.CT kappa pp) × S.SAIdealState Sim kappa pp)
  | (st, none) => (Sim.enc kappa pp st x).bind fun o => .pure (some o.1, o.2, some ⟨x, y⟩)
  | (st, some a) => .pure (none, st, some a)

/-- The first ideal challenge uses public-input-only simulation and records the pair. -/
theorem idealSAChallenge_none (Sim : SASimulator.Raw S) (kappa : ℕ)
    (pp : PublicParams S.G kappa) (x : Fin (C.pubLen.eval kappa) → Bool)
    (y : Fin (C.privLen.eval kappa) → Bool) (st : Sim.St kappa pp) :
    S.idealSAChallenge Sim kappa pp x y (st, none) =
      (Sim.enc kappa pp st x).bind fun o => .pure (some o.1, o.2, some ⟨x, y⟩) := rfl

/-- A repeated ideal challenge fails without changing either state component. -/
theorem idealSAChallenge_some (Sim : SASimulator.Raw S) (kappa : ℕ)
    (pp : PublicParams S.G kappa) (x : Fin (C.pubLen.eval kappa) → Bool)
    (y : Fin (C.privLen.eval kappa) → Bool) (st : Sim.St kappa pp)
    (a : SAChallenge C kappa) :
    S.idealSAChallenge Sim kappa pp x y (st, some a) = .pure (none, st, some a) := rfl

/-- The ideal key handler supplies exactly the function's allowed scalar to the
stateful simulator, rejecting queries before the challenge. [Wee20, §2.2, p.5]. -/
noncomputable def idealSAKey (Sim : SASimulator.Raw S) (kappa : ℕ)
    (pp : PublicParams S.G kappa) (f : Fin (C.fnLen.eval kappa) → Bool) :
    S.SAIdealState Sim kappa pp →
      ProbComp (Option (S.SK kappa pp) × S.SAIdealState Sim kappa pp)
  | (st, none) => .pure (none, st, none)
  | (st, some a) =>
    (Sim.key kappa pp st a.publicInput f
      (C.eval kappa (S.cprm kappa pp) f a.publicInput a.privateInput)).bind fun o =>
        .pure (some o.1, o.2, some a)

/-- An ideal key request before the challenge fails. -/
theorem idealSAKey_none (Sim : SASimulator.Raw S) (kappa : ℕ)
    (pp : PublicParams S.G kappa) (f : Fin (C.fnLen.eval kappa) → Bool)
    (st : Sim.St kappa pp) :
    S.idealSAKey Sim kappa pp f (st, none) = .pure (none, st, none) := rfl

/-- An ideal key request after the challenge uses precisely its allowed scalar. -/
theorem idealSAKey_some (Sim : SASimulator.Raw S) (kappa : ℕ)
    (pp : PublicParams S.G kappa) (f : Fin (C.fnLen.eval kappa) → Bool)
    (st : Sim.St kappa pp) (a : SAChallenge C kappa) :
    S.idealSAKey Sim kappa pp f (st, some a) =
      (Sim.key kappa pp st a.publicInput f
        (C.eval kappa (S.cprm kappa pp) f a.publicInput a.privateInput)).bind fun o =>
          .pure (some o.1, o.2, some a) := rfl

/-- The real oracle implementation is the wire adapter of the honest typed handlers. -/
noncomputable def realSAImpl (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (msk : S.MSK kappa pp) :
    QueryImpl (S.saSpec kappa) (S.SAState kappa) unifSpec :=
  S.saImpl kappa pp (S.realSAChallenge kappa pp pk) (S.realSAKey kappa pp msk)

/-- The real implementation is exactly the displayed adapter. -/
theorem realSAImpl_eq (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (msk : S.MSK kappa pp) : S.realSAImpl kappa pp pk msk =
    S.saImpl kappa pp (S.realSAChallenge kappa pp pk) (S.realSAKey kappa pp msk) := rfl

/-- The ideal oracle implementation adapts its stateful typed simulation handlers. -/
noncomputable def idealSAImpl (Sim : SASimulator.Raw S) (kappa : ℕ)
    (pp : PublicParams S.G kappa) :
    QueryImpl (S.saSpec kappa) (S.SAIdealState Sim kappa pp) unifSpec :=
  S.saImpl kappa pp (S.idealSAChallenge Sim kappa pp) (S.idealSAKey Sim kappa pp)

/-- The ideal implementation is exactly the displayed adapter. -/
theorem idealSAImpl_eq (Sim : SASimulator.Raw S) (kappa : ℕ)
    (pp : PublicParams S.G kappa) : S.idealSAImpl Sim kappa pp =
    S.saImpl kappa pp (S.idealSAChallenge Sim kappa pp) (S.idealSAKey Sim kappa pp) := rfl

/-- The semi-adaptive game first generates pp and the public key, then runs the
bounded adversary with one independent coin tape. True selects the real experiment.
[Wee20, §2.2, p.5]. -/
noncomputable def saGame (Sim : SASimulator.Raw S) (A : S.SAAdv) (real : Bool)
    (kappa : ℕ) : ProbComp Bool :=
  (S.pubGen kappa).bind fun pp =>
    if real then
      (S.setup kappa pp).bind fun k =>
      (ProbComp.sample (Fin (A.coins.eval kappa) → Bool)).bind fun r =>
        Prod.fst <$> simulate (S.realSAImpl kappa pp k.1 k.2)
          (A.run kappa pp k.1 (List.ofFn r)) none
    else
      (Sim.setup kappa pp).bind fun k =>
      (ProbComp.sample (Fin (A.coins.eval kappa) → Bool)).bind fun r =>
        Prod.fst <$> simulate (S.idealSAImpl Sim kappa pp)
          (A.run kappa pp k.1 (List.ofFn r)) (k.2, none)

/-- The complete game is the displayed exact stateful experiment. -/
theorem saGame_eq (Sim : SASimulator.Raw S) (A : S.SAAdv) (real : Bool) (kappa : ℕ) :
    S.saGame Sim A real kappa = (S.pubGen kappa).bind fun pp =>
      if real then
        (S.setup kappa pp).bind fun k =>
        (ProbComp.sample (Fin (A.coins.eval kappa) → Bool)).bind fun r =>
          Prod.fst <$> simulate (S.realSAImpl kappa pp k.1 k.2)
            (A.run kappa pp k.1 (List.ofFn r)) none
      else
        (Sim.setup kappa pp).bind fun k =>
        (ProbComp.sample (Fin (A.coins.eval kappa) → Bool)).bind fun r =>
          Prod.fst <$> simulate (S.idealSAImpl Sim kappa pp)
            (A.run kappa pp k.1 (List.ofFn r)) (k.2, none) := rfl

/-- Semi-adaptive simulation advantage is the common two-experiment advantage.
[Wee20, §2.2, p.5]. -/
noncomputable def saSimAdv (Sim : SASimulator.Raw S) (A : S.SAAdv) (kappa : ℕ) : ℝ :=
  advantage (S.saGame Sim A true kappa) (S.saGame Sim A false kappa)

/-- Semi-adaptive advantage is the displayed real/ideal difference. -/
theorem saSimAdv_eq (Sim : SASimulator.Raw S) (A : S.SAAdv) (kappa : ℕ) :
    S.saSimAdv Sim A kappa =
      advantage (S.saGame Sim A true kappa) (S.saGame Sim A false kappa) := rfl

end FEScheme.Raw
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
