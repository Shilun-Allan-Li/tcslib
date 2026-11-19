/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.TwoStage
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Correctness
import TCSlib.Cryptography.Games.Advantage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The committed simulation experiment

The first machine runs before public-parameter generation. The real experiment uses honest
setup, encryption and the ordered committed keys. The ideal experiment uses one simulator,
threading its state through encryption and every key. Both feed the same encoded public view
to the second machine. All draws are exact and are sequenced in their displayed order.

## Main definitions

* `FEScheme.Raw.viewWord`: the public view supplied to the second machine.
* `FEScheme.Raw.realView`, `idealView`: the two public-view laws.
* `FEScheme.Raw.simGame`, `simAdv`: the two-stage experiment and its advantage.

## Main results

Every experiment has an equation reader exposing its complete sampling law.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definition 4.3 and Remarks 4.3 and 4.6.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

namespace FEScheme.Raw

variable {C : FnClass} (S : FEScheme.Raw C)

/-- Encode an already represented public view, retaining the committed key order.
This shared word constructor permits a wire adversary to retain answers without decoding
arbitrary scheme objects [GJLS21, Definition 4.3]. -/
def viewWordBits {q : PolyExpr} {κ : ℕ} (a : Commitment C q κ)
    (pp : PublicParams S.G κ) (pk : Fin (S.mpkLen.eval κ) → Bool)
    (keys : List (Fin (S.skLen.eval κ) → Bool))
    (ct : Fin (S.ctLen.eval κ) → Bool) : List Bool :=
  pairEncode a.state (pairEncode pp.encode
    (pairEncode (List.ofFn pk)
      (pairEncode (PrivateKeyScheme.encodeList (keys.map List.ofFn))
        (pairEncode (List.ofFn a.publicInput) (List.ofFn ct)))))

/-- The represented view has the displayed nested encoding in committed key order. -/
theorem viewWordBits_eq {q : PolyExpr} {κ : ℕ} (a : Commitment C q κ)
    (pp : PublicParams S.G κ) (pk : Fin (S.mpkLen.eval κ) → Bool)
    (keys : List (Fin (S.skLen.eval κ) → Bool))
    (ct : Fin (S.ctLen.eval κ) → Bool) :
    S.viewWordBits a pp pk keys ct = pairEncode a.state (pairEncode pp.encode
      (pairEncode (List.ofFn pk)
        (pairEncode (PrivateKeyScheme.encodeList (keys.map List.ofFn))
          (pairEncode (List.ofFn a.publicInput) (List.ofFn ct))))) := rfl

/-- Encode the first-stage state and the view `(pp, pk, keys, x, ct)` supplied to the
second machine [GJLS21, Definition 4.3, at epsilon one; Remark 4.6]. -/
def viewWord {q : PolyExpr} {κ : ℕ} (a : Commitment C q κ)
    (pp : PublicParams S.G κ) (pk : S.MPK κ pp) (keys : List (S.SK κ pp))
    (ct : S.CT κ pp) : List Bool :=
  S.viewWordBits a pp (S.encMPK κ pp pk) (keys.map (S.encSK κ pp))
    (S.encCT κ pp ct)

/-- The second-stage word is the displayed nested pair in committed key order. -/
theorem viewWord_eq {q : PolyExpr} {κ : ℕ} (a : Commitment C q κ)
    (pp : PublicParams S.G κ) (pk : S.MPK κ pp) (keys : List (S.SK κ pp))
    (ct : S.CT κ pp) :
    S.viewWord a pp pk keys ct = pairEncode a.state (pairEncode pp.encode
      (pairEncode (List.ofFn (S.encMPK κ pp pk))
        (pairEncode (PrivateKeyScheme.encodeList (keys.map fun sk => List.ofFn (S.encSK κ pp sk)))
          (pairEncode (List.ofFn a.publicInput) (List.ofFn (S.encCT κ pp ct)))))) :=
  congrArg (fun k : List (List Bool) => pairEncode a.state (pairEncode pp.encode
    (pairEncode (List.ofFn (S.encMPK κ pp pk))
      (pairEncode (PrivateKeyScheme.encodeList k)
        (pairEncode (List.ofFn a.publicInput) (List.ofFn (S.encCT κ pp ct)))))))
    (List.map_map (f := S.encSK κ pp) (g := List.ofFn) (l := keys))

/-- Encoding the typed view applies the shared represented-view constructor to its encodings. -/
theorem viewWord_eq_viewWordBits {q : PolyExpr} {κ : ℕ} (a : Commitment C q κ)
    (pp : PublicParams S.G κ) (pk : S.MPK κ pp) (keys : List (S.SK κ pp))
    (ct : S.CT κ pp) :
    S.viewWord a pp pk keys ct = S.viewWordBits a pp (S.encMPK κ pp pk)
      (keys.map (S.encSK κ pp)) (S.encCT κ pp ct) := rfl

/-- Produce the real view after the commitment is fixed. Keys are sampled in increasing
committed order using the shared monadic list traversal [GJLS21, Definition 4.3]. -/
noncomputable def realView {q : PolyExpr} {κ : ℕ} (a : Commitment C q κ) :
    ProbComp (List Bool) :=
  (S.pubGen κ).bind fun pp =>
  (S.setup κ pp).bind fun k =>
  (S.enc κ pp k.1 a.publicInput a.privateInput).bind fun ct =>
  (List.mapM (fun j => S.keyGen κ pp k.2 (a.functions j))
    (List.finRange (q.eval κ))).bind fun keys =>
      .pure (S.viewWord a pp k.1 keys ct)

/-- The real view is exactly the displayed sequential experiment. -/
theorem realView_eq {q : PolyExpr} {κ : ℕ} (a : Commitment C q κ) :
    S.realView a =
      (S.pubGen κ).bind fun pp =>
      (S.setup κ pp).bind fun k =>
      (S.enc κ pp k.1 a.publicInput a.privateInput).bind fun ct =>
      (List.mapM (fun j => S.keyGen κ pp k.2 (a.functions j))
        (List.finRange (q.eval κ))).bind fun keys =>
          .pure (S.viewWord a pp k.1 keys ct) := rfl

/-- Produce the ideal view from the allowed information. State is threaded through
ciphertext simulation and then all committed keys [GJLS21, Definition 4.3]. -/
noncomputable def idealView (Sim : Simulator.Raw S) {q : PolyExpr} {κ : ℕ}
    (a : Commitment C q κ) : ProbComp (List Bool) :=
  (S.pubGen κ).bind fun pp =>
  (Sim.setup κ pp).bind fun k =>
  (Sim.enc κ pp k.2 (a.omega S pp)).bind fun cst =>
  (List.mapM (m := StateT (Sim.St κ pp) ProbComp)
    (fun j st => Sim.key κ pp st (a.omega S pp) j)
    (List.finRange (q.eval κ)) cst.2).bind fun keys =>
      .pure (S.viewWord a pp k.1 keys.1 cst.1)

/-- The ideal view is exactly the displayed state-threaded experiment. -/
theorem idealView_eq (Sim : Simulator.Raw S) {q : PolyExpr} {κ : ℕ}
    (a : Commitment C q κ) : S.idealView Sim a =
      (S.pubGen κ).bind fun pp =>
      (Sim.setup κ pp).bind fun k =>
      (Sim.enc κ pp k.2 (a.omega S pp)).bind fun cst =>
      (List.mapM (m := StateT (Sim.St κ pp) ProbComp)
        (fun j st => Sim.key κ pp st (a.omega S pp) j)
        (List.finRange (q.eval κ)) cst.2).bind fun keys =>
          .pure (S.viewWord a pp k.1 keys.1 cst.1) := rfl

/-- The committed simulation game draws first-stage coins before pp, then gives the
chosen public view to the second machine with independent coins
[GJLS21, Definition 4.3, epsilon one; Remark 4.6]. The Boolean flag selects real when true. -/
noncomputable def simGame (Sim : Simulator.Raw S) (A : TwoStage)
    (q : PolyExpr) (real : Bool) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (A.first.Coins κ)).bind fun r₁ =>
    let a := Commitment.decode C q κ (A.first.runAt κ [] r₁)
    (if real then S.realView a else S.idealView Sim a).bind fun v =>
    (ProbComp.sample (A.second.Coins κ)).bind fun r₂ =>
      .pure (A.second.distinguisherL κ v r₂)

/-- The simulation game is the displayed two-stage machine experiment. -/
theorem simGame_eq (Sim : Simulator.Raw S) (A : TwoStage)
    (q : PolyExpr) (real : Bool) (κ : ℕ) : S.simGame Sim A q real κ =
      (ProbComp.sample (A.first.Coins κ)).bind fun r₁ =>
        let a := Commitment.decode C q κ (A.first.runAt κ [] r₁)
        (if real then S.realView a else S.idealView Sim a).bind fun v =>
        (ProbComp.sample (A.second.Coins κ)).bind fun r₂ =>
          .pure (A.second.distinguisherL κ v r₂) := rfl

/-- Simulation advantage is the absolute difference of real and ideal acceptance
probabilities [GJLS21, Definition 4.3, epsilon one]. -/
noncomputable def simAdv (Sim : Simulator.Raw S) (A : TwoStage) (q : PolyExpr)
    (κ : ℕ) : ℝ := advantage (S.simGame Sim A q true κ) (S.simGame Sim A q false κ)

/-- Simulation advantage uses the common two-experiment convention. -/
theorem simAdv_eq (Sim : Simulator.Raw S) (A : TwoStage) (q : PolyExpr) (κ : ℕ) :
    S.simAdv Sim A q κ = advantage (S.simGame Sim A q true κ)
      (S.simGame Sim A q false κ) := rfl

end FEScheme.Raw

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
