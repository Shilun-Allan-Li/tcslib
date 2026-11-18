/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Security
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Committed simulation as a semi-adaptive experiment

A raw semi-adaptive simulator supplies a raw committed simulator by projecting the
allowed information to its public input and indexed function/value. A two-stage
adversary becomes a typed next-move adversary with disjoint first/second coin blocks,
one challenge followed by its committed keys, and total budget q+1.

The identity below concerns exact laws. The two experiments sample independent
coins in different orders, so their OracleComp syntax trees are not asserted equal.
No efficient simulator conversion or oracle-machine construction is claimed.

## Main definitions

* `SASimulator.Raw.toSim`: the raw stateful simulator conversion.
* `TwoStage.toSA`: the committed machine pair as a typed semi-adaptive adversary.

## Main results

* `expect_simGame_eq_saGame`: the two experiments have identical laws.
* `simAdv_eq_saSimAdv`: committed advantage is exactly the derived semi-adaptive advantage.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; ePrint 2020/764, Definition 4.3, epsilon one, Remark 4.6.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; ePrint 2020/1420, §2.2, p.5.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open TCSlib.Cryptography.Pairing
open Complexity Turing TCSlib.Cryptography.Games

namespace FEScheme.Raw.SASimulator.Raw

variable {C : FnClass} {S : FEScheme.Raw C} (Sim : FEScheme.Raw.SASimulator.Raw S)

/-- A semi-adaptive raw simulator yields the committed raw simulator by passing
only omega.publicInput to encryption and the indexed function/scalar to key simulation.
[GJLS21, Definition 4.3; Wee20, §2.2, p.5]. Draws remain the same single draw types. -/
def toSim : FEScheme.Raw.Simulator.Raw S where
  St := Sim.St
  encSt := Sim.encSt
  encSt_injective := Sim.encSt_injective
  SetupDraw := Sim.SetupDraw
  setupFinite := Sim.setupFinite
  setupNonempty := Sim.setupNonempty
  setupCore := Sim.setupCore
  EncDraw := fun kappa pp st omega => Sim.EncDraw kappa pp st omega.publicInput
  encFinite := fun kappa pp st omega => Sim.encFinite kappa pp st omega.publicInput
  encNonempty := fun kappa pp st omega => Sim.encNonempty kappa pp st omega.publicInput
  encCore := fun kappa pp st omega => Sim.encCore kappa pp st omega.publicInput
  KeyDraw := fun kappa pp st omega j =>
    Sim.KeyDraw kappa pp st omega.publicInput (omega.functions j) (omega.values j)
  keyFinite := fun kappa pp st omega j =>
    Sim.keyFinite kappa pp st omega.publicInput (omega.functions j) (omega.values j)
  keyNonempty := fun kappa pp st omega j =>
    Sim.keyNonempty kappa pp st omega.publicInput (omega.functions j) (omega.values j)
  keyCore := fun kappa pp st omega j =>
    Sim.keyCore kappa pp st omega.publicInput (omega.functions j) (omega.values j)
  encSetupDraw := Sim.encSetupDraw
  encEncDraw := fun kappa pp st omega => Sim.encEncDraw kappa pp st omega.publicInput
  encKeyDraw := fun kappa pp st omega j =>
    Sim.encKeyDraw kappa pp st omega.publicInput (omega.functions j) (omega.values j)

/-- The converted simulator retains the same state family. -/
theorem toSim_St : Sim.toSim.St = Sim.St := rfl

/-- The converted simulator retains the same canonical state encoding. -/
theorem toSim_encSt : Sim.toSim.encSt = Sim.encSt := rfl

/-- The converted simulator retains the complete setup draw family. -/
theorem toSim_SetupDraw : Sim.toSim.SetupDraw = Sim.SetupDraw := rfl

/-- The converted simulator retains the original deterministic setup core. -/
theorem toSim_setupCore : Sim.toSim.setupCore = Sim.setupCore := rfl

/-- The converted ciphertext draw depends only on the allowed public input. -/
theorem toSim_EncDraw (kappa : ℕ) (pp : PublicParams S.G kappa)
    (st : Sim.St kappa pp) (omega : S.Omega kappa pp) :
    Sim.toSim.EncDraw kappa pp st omega = Sim.EncDraw kappa pp st omega.publicInput := rfl

/-- The converted ciphertext core passes only the public input to the raw simulator. -/
theorem toSim_encCore (kappa : ℕ) (pp : PublicParams S.G kappa)
    (st : Sim.St kappa pp) (omega : S.Omega kappa pp) :
    Sim.toSim.encCore kappa pp st omega = Sim.encCore kappa pp st omega.publicInput := rfl

/-- The converted key draw uses the indexed function and scalar value. -/
theorem toSim_KeyDraw (kappa : ℕ) (pp : PublicParams S.G kappa)
    (st : Sim.St kappa pp) (omega : S.Omega kappa pp) (j : Fin omega.count) :
    Sim.toSim.KeyDraw kappa pp st omega j =
      Sim.KeyDraw kappa pp st omega.publicInput (omega.functions j) (omega.values j) := rfl

/-- The converted key core uses the indexed function and scalar value. -/
theorem toSim_keyCore (kappa : ℕ) (pp : PublicParams S.G kappa)
    (st : Sim.St kappa pp) (omega : S.Omega kappa pp) (j : Fin omega.count) :
    Sim.toSim.keyCore kappa pp st omega j =
      Sim.keyCore kappa pp st omega.publicInput (omega.functions j) (omega.values j) := rfl

/-- The converted exact setup algorithm is the original semi-adaptive setup. -/
theorem toSim_setup (kappa : ℕ) (pp : PublicParams S.G kappa) :
    Sim.toSim.setup kappa pp = Sim.setup kappa pp :=
  (FEScheme.Raw.Simulator.Raw.setup_eq Sim.toSim kappa pp).trans
    (setup_eq Sim kappa pp).symm

/-- Converted exact ciphertext simulation is precisely public-input-only simulation. -/
theorem toSim_enc (kappa : ℕ) (pp : PublicParams S.G kappa)
    (st : Sim.St kappa pp) (omega : S.Omega kappa pp) :
    Sim.toSim.enc kappa pp st omega = Sim.enc kappa pp st omega.publicInput :=
  (FEScheme.Raw.Simulator.Raw.enc_eq Sim.toSim kappa pp st omega).trans
    (enc_eq Sim kappa pp st omega.publicInput).symm

/-- Converted exact key simulation is precisely the indexed function/scalar simulation. -/
theorem toSim_key (kappa : ℕ) (pp : PublicParams S.G kappa)
    (st : Sim.St kappa pp) (omega : S.Omega kappa pp) (j : Fin omega.count) :
    Sim.toSim.key kappa pp st omega j =
      Sim.key kappa pp st omega.publicInput (omega.functions j) (omega.values j) :=
  (FEScheme.Raw.Simulator.Raw.key_eq Sim.toSim kappa pp st omega j).trans
    (key_eq Sim kappa pp st omega.publicInput (omega.functions j) (omega.values j)).symm

end FEScheme.Raw.SASimulator.Raw

namespace TwoStage

/-- The first machine uses the first block of the composed adversary's tape.
This is deterministic coin-layout glue, not a sampler or an assumption reduction. -/
def firstCoins (A : TwoStage) (kappa : ℕ) (r : List Bool) : A.first.Coins kappa :=
  fun i => r.getD i.val false

/-- The first coin block is read from the tape's initial coordinates. -/
theorem firstCoins_eq (A : TwoStage) (kappa : ℕ) (r : List Bool) :
    A.firstCoins kappa r = fun i => r.getD i.val false := rfl

/-- The second machine uses the disjoint block immediately after the first coins. -/
def secondCoins (A : TwoStage) (kappa : ℕ) (r : List Bool) : A.second.Coins kappa :=
  fun i => r.getD (A.first.coinLen kappa + i.val) false

/-- The second coin block starts exactly after the first machine's coin count. -/
theorem secondCoins_eq (A : TwoStage) (kappa : ℕ) (r : List Bool) :
    A.secondCoins kappa r = fun i => r.getD (A.first.coinLen kappa + i.val) false := rfl

/-- The first machine's commitment depends only on its coin block, before it can
observe pp or pk. [GJLS21, Definition 4.3]. -/
def saCommitment (A : TwoStage) (C : FnClass) (q : PolyExpr) (kappa : ℕ)
    (r : List Bool) : Commitment C q kappa :=
  Commitment.decode C q kappa (A.first.runAt kappa [] (A.firstCoins kappa r))

/-- The commitment is the canonical parser of the first machine's activation. -/
theorem saCommitment_eq (A : TwoStage) (C : FnClass) (q : PolyExpr) (kappa : ℕ)
    (r : List Bool) : A.saCommitment C q kappa r =
    Commitment.decode C q kappa (A.first.runAt kappa [] (A.firstCoins kappa r)) := rfl

/-- The next move first asks the committed challenge, then each committed key in
order, and finally runs the second machine on the canonical public view. Failed
challenge answers return false. No ciphertext or key encoding is inverted.
[GJLS21, Definition 4.3; Wee20, §2.2, p.5], exact typed embedding. -/
def saNext {C : FnClass} {S : FEScheme.Raw C} (A : TwoStage) (q : PolyExpr)
    (kappa : ℕ) (pp : PublicParams S.G kappa) (pk : S.MPK kappa pp)
    (r : List Bool) (hist : QueryLog (S.saSpec kappa)) : Move (S.saSpec kappa) Bool :=
  let a := A.saCommitment C q kappa r
  match hist with
  | [] => S.saChallengeMove kappa a.publicInput a.privateInput
  | e :: es =>
    match S.saCTPayload kappa e.1 e.2.2 with
    | none => .ret false
    | some ct =>
      if h : es.length < q.eval kappa then
        S.saKeyMove kappa (a.functions ⟨es.length, h⟩)
      else
        let keys := es.filterMap fun entry => S.saSKPayload kappa entry.1 entry.2.2
        .ret (A.second.distinguisherL kappa
          (S.viewWordBits a pp (S.encMPK kappa pp pk) keys ct) (A.secondCoins kappa r))

/-- On the empty history the embedded adversary asks its committed challenge. -/
theorem saNext_nil {C : FnClass} {S : FEScheme.Raw C} (A : TwoStage) (q : PolyExpr)
    (kappa : ℕ) (pp : PublicParams S.G kappa) (pk : S.MPK kappa pp) (r : List Bool) :
    A.saNext (S := S) q kappa pp pk r [] =
      S.saChallengeMove kappa (A.saCommitment C q kappa r).publicInput
        (A.saCommitment C q kappa r).privateInput := rfl

/-- After the challenge the embedded adversary reads its payload, requests the
next committed key, or supplies the collected wire payloads to the second machine. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem saNext_cons {C : FnClass} {S : FEScheme.Raw C} (A : TwoStage) (q : PolyExpr)
    (kappa : ℕ) (pp : PublicParams S.G kappa) (pk : S.MPK kappa pp) (r : List Bool)
    (e : Sigma fun i => (S.saSpec kappa).dom i × (S.saSpec kappa).rng i)
    (es : QueryLog (S.saSpec kappa)) :
    A.saNext (S := S) q kappa pp pk r (e :: es) =
      let a := A.saCommitment C q kappa r
      match S.saCTPayload kappa e.1 e.2.2 with
      | none => .ret false
      | some ct =>
        if h : es.length < q.eval kappa then
          S.saKeyMove kappa (a.functions ⟨es.length, h⟩)
        else
          let keys := es.filterMap fun entry => S.saSKPayload kappa entry.1 entry.2.2
          .ret (A.second.distinguisherL kappa
            (S.viewWordBits a pp (S.encMPK kappa pp pk) keys ct) (A.secondCoins kappa r)) := rfl

/-- A committed machine pair becomes a typed semi-adaptive adversary with a total
budget of q+1 calls and concatenated independent coin blocks. The first stage
ignores pp and pk; the second sees exactly the specified public view.
[GJLS21, Definition 4.3; Wee20, §2.2, p.5]. This constructs no oracle NUPPT. -/
def toSA {C : FnClass} {S : FEScheme.Raw C} (A : TwoStage) (q : PolyExpr) : S.SAAdv where
  coins := .add A.first.coins A.second.coins
  budget := .add q (PolyExpr.const 1)
  next := A.saNext (S := S) q

/-- The composed tape has the sum of the two original coin polynomials. -/
theorem toSA_coins {C : FnClass} {S : FEScheme.Raw C} (A : TwoStage) (q : PolyExpr) :
    (A.toSA (S := S) q).coins = .add A.first.coins A.second.coins := rfl

/-- The total query budget is exactly one challenge plus q keys. -/
theorem toSA_budget {C : FnClass} {S : FEScheme.Raw C} (A : TwoStage) (q : PolyExpr) :
    (A.toSA (S := S) q).budget = .add q (PolyExpr.const 1) := rfl

/-- The embedded next move is the explicit committed protocol above. -/
theorem toSA_next {C : FnClass} {S : FEScheme.Raw C} (A : TwoStage) (q : PolyExpr) :
    (A.toSA (S := S) q).next = A.saNext (S := S) q := rfl

/-- The embedded adversary uses the existing bounded interpreter at q+1 total calls. -/
theorem toSA_run {C : FnClass} {S : FEScheme.Raw C} (A : TwoStage) (q : PolyExpr)
    (kappa : ℕ) (pp : PublicParams S.G kappa) (pk : S.MPK kappa pp) (r : List Bool) :
    (A.toSA (S := S) q).run kappa pp pk r =
      buildComp (A.saNext (S := S) q kappa pp pk r) false (q.eval kappa + 1) [] :=
  FEScheme.Raw.SAAdv.run_eq (A.toSA (S := S) q) kappa pp pk r

end TwoStage

namespace FEScheme.Raw

variable {C : FnClass} (S : FEScheme.Raw C)

/-- The committed and derived semi-adaptive games have exactly the same laws.
[GJLS21, Definition 4.3; Wee20, §2.2, p.5]. This is expectation equality, since
independent draws occur in different syntactic orders.

**Proof sketch.** Reindex the composed tape by the finite-sum equivalence into
first-stage and second-stage tapes, using the shared coin-polynomial readers.
Commute the first-stage tape before pp/setup; its activation ignores the public
view. Unroll buildComp through its published case lemmas for one challenge and
q ordered key calls. The typed handler cases give the same state-threaded key
law as List.mapM. Convert the simulator through the toSim readers and identify
the second-stage word through viewWord_eq_viewWordBits. -/
theorem expect_simGame_eq_saGame (Sim : FEScheme.Raw.SASimulator.Raw S) (A : TwoStage)
    (q : PolyExpr) (real : Bool) (kappa : ℕ) (test : Bool → ℝ) :
    ProbComp.expect (S.simGame Sim.toSim A q real kappa) test =
      ProbComp.expect (S.saGame Sim (A.toSA (S := S) q) real kappa) test := sorry

/-- The committed simulation advantage equals the semi-adaptive advantage of its
explicit typed embedding, with no loss. [GJLS21, Definition 4.3; Wee20, §2.2].

**Proof sketch.** Apply the preceding exact law identity to each experiment's
acceptance test, then read the two advantages through their published equations. -/
theorem simAdv_eq_saSimAdv (Sim : FEScheme.Raw.SASimulator.Raw S) (A : TwoStage)
    (q : PolyExpr) (kappa : ℕ) :
    S.simAdv Sim.toSim A q kappa = S.saSimAdv Sim (A.toSA (S := S) q) kappa := sorry

end FEScheme.Raw
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
