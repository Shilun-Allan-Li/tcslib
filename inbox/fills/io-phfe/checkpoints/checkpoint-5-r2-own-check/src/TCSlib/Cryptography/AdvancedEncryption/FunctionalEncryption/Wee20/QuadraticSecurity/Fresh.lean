/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The actual fresh quadratic semi-adaptive experiments

## Main definitions

* `Wee20.Quadratic.freshRealHandler`: actual fresh honest encryption and key generation.
* `Wee20.Quadratic.FreshIdealState`, `freshIdealHandler`: actual stateful simulator calls.
* `Wee20.Quadratic.freshSaGame`, `freshSaSimAdv`: fresh raw endpoint laws and advantage.

## Main results

Readers expose every fresh raw call and the simulator's updated state. The substantive
padded-to-fresh endpoint coupling is stated in `Theorems`.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §2.2, p. 5,
  §3.1, p. 6 and §3.2, p. 7. The allowed value is supplied in the source group.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

/-- Honest accepted queries invoke the actual fresh raw laws [Wee20, §3.1, p. 6]. -/
noncomputable def freshRealHandler (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (pk : MPK G ℓ n1 n2 κ pp)
    (msk : MSK G ℓ n1 n2 κ pp) :
    QueryImpl (saSpec G n1 n2 PG κ pp) (SAState G ℓ n1 n2 κ pp) unifSpec
  | false, msg, st => match st.challenge with
    | none => ((fun ct => (some ct, ⟨some msg, st.used⟩)) <$> (enc G ℓ n1 n2 κ pp pk msg.1 msg.2.1
      msg.2.2))
    | some _ => .pure (none, st)
  | true, f, st => match st.challenge with
    | none => .pure (none, st)
    | some _ => if st.used < q.eval κ then
        ((fun key => (some ⟨f, key⟩, ⟨st.challenge, st.used + 1⟩)) <$> (keyGen G n1 n2 PG κ pp msk
          f))
      else .pure (none, st)

/-- A real challenge samples the actual honest encryption draw exactly once. -/
theorem freshRealHandler_challenge (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (pk : MPK G ℓ n1 n2 κ pp)
    (msk : MSK G ℓ n1 n2 κ pp) (msg : Challenge G ℓ n1 n2 κ pp)
    (st : SAState G ℓ n1 n2 κ pp) :
    freshRealHandler G n1 n2 q PG κ pp pk msk false msg st =
      match st.challenge with
      | none => ((fun ct => (some ct, ⟨some msg, st.used⟩)) <$> (enc G ℓ n1 n2 κ pp pk msg.1 msg.2.1
        msg.2.2))
      | some _ => .pure (none, st) := rfl

/-- An accepted real key samples its actual function-dependent draw. -/
theorem freshRealHandler_key (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (pk : MPK G ℓ n1 n2 κ pp)
    (msk : MSK G ℓ n1 n2 κ pp) (f : Fn κ pp.orderParam)
    (st : SAState G ℓ n1 n2 κ pp) : freshRealHandler G n1 n2 q PG κ pp pk msk true f st =
      match st.challenge with
      | none => .pure (none, st)
      | some _ => if st.used < q.eval κ then
          ((fun key => (some ⟨f, key⟩, ⟨st.challenge, st.used + 1⟩)) <$> (keyGen G n1 n2 PG κ pp msk
            f))
        else .pure (none, st) := rfl

/-- The ideal experiment retains both protocol state and the actual updated simulator
state [Wee20, §3.2, p. 7]. The y vectors are saved by its accepted encryption call. -/
structure FreshIdealState (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) where
  /-- Challenge and accepted-key counter. -/
  protocol : SAState G ℓ n1 n2 κ pp
  /-- Persistent simulator state. -/
  simulator : SimState G ℓ n1 n2 κ pp

/-- Ideal accepted queries invoke actual stateful simulator calls
[Wee20, §3.2, p. 7]. The key's allowed value is exponentiated from the known scalar
function value; no target-to-source conversion is attempted. -/
noncomputable def freshIdealHandler (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) :
    QueryImpl (saSpec G n1 n2 PG κ pp) (FreshIdealState G ℓ n1 n2 κ pp) unifSpec
  | false, msg, st => match st.protocol.challenge with
    | none => ((fun out => (some out.1, ⟨⟨some msg, st.protocol.used⟩, out.2⟩)) <$> (simEnc G ℓ n1
      n2 κ pp st.simulator msg.1))
    | some _ => .pure (none, st)
  | true, f, st => match st.protocol.challenge with
    | none => .pure (none, st)
    | some msg => if st.protocol.used < q.eval κ then
        ((fun key => (some ⟨f, key⟩,
            ⟨⟨st.protocol.challenge, st.protocol.used + 1⟩, st.simulator⟩)) <$> (simKey G n1 n2 PG κ
              pp st.simulator f msg.1
          (pp.generator ^ (value G n1 n2 PG κ pp f msg.1 msg.2.1 msg.2.2).val)))
      else .pure (none, st)

/-- Ideal encryption saves precisely the state returned by the actual simulator. -/
theorem freshIdealHandler_challenge (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (msg : Challenge G ℓ n1 n2 κ pp)
    (st : FreshIdealState G ℓ n1 n2 κ pp) :
    freshIdealHandler G n1 n2 q PG κ pp false msg st =
      match st.protocol.challenge with
      | none => ((fun out => (some out.1, ⟨⟨some msg, st.protocol.used⟩, out.2⟩)) <$> (simEnc G ℓ n1
        n2 κ pp st.simulator msg.1))
      | some _ => .pure (none, st) := rfl

/-- Ideal keys retain the simulator state and use the exact allowed scalar value. -/
theorem freshIdealHandler_key (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (st : FreshIdealState G ℓ n1 n2 κ pp) : freshIdealHandler G n1 n2 q PG κ pp true f st =
      match st.protocol.challenge with
      | none => .pure (none, st)
      | some msg => if st.protocol.used < q.eval κ then
          ((fun key => (some ⟨f, key⟩,
              ⟨⟨st.protocol.challenge, st.protocol.used + 1⟩, st.simulator⟩)) <$> (simKey G n1 n2 PG
                κ pp st.simulator f msg.1
            (pp.generator ^ (value G n1 n2 PG κ pp f msg.1 msg.2.1 msg.2.2).val)))
        else .pure (none, st) := rfl

/-- The actual raw endpoint experiment calls setup or simSetup, then the actual fresh
stateful oracles [Wee20, §2.2, p. 5; §3.1–§3.2, pp. 6–7]. -/
noncomputable def freshSaGame (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (ideal : Bool) (κ : ℕ) : ProbComp Bool :=
  (publicParamsGen G κ).bind fun pp =>
  (ProbComp.sample (Fin (A.coins.eval κ) → Bool)).bind fun r =>
  if ideal then (simSetup G ℓ n1 n2 κ pp).bind fun ctx =>
    ((Prod.fst) <$> (simulate (freshIdealHandler G n1 n2 A.budget PG κ pp)
      (SAAdv.run G n1 n2 PG A κ pp ctx.1 (List.ofFn r))
      ⟨⟨none, 0⟩, ctx.2⟩))
  else (setup G ℓ n1 n2 κ pp).bind fun ctx =>
    ((Prod.fst) <$> (simulate (freshRealHandler G n1 n2 A.budget PG κ pp ctx.1 ctx.2)
      (SAAdv.run G n1 n2 PG A κ pp ctx.1 (List.ofFn r)) ⟨none, 0⟩))

/-- Fresh endpoint laws expose their actual setup and stateful interaction. -/
theorem freshSaGame_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (ideal : Bool) (κ : ℕ) : freshSaGame G n1 n2 PG A ideal κ =
      (publicParamsGen G κ).bind fun pp =>
      (ProbComp.sample (Fin (A.coins.eval κ) → Bool)).bind fun r =>
      if ideal then (simSetup G ℓ n1 n2 κ pp).bind fun ctx =>
        ((Prod.fst) <$> (simulate (freshIdealHandler G n1 n2 A.budget PG κ pp)
          (SAAdv.run G n1 n2 PG A κ pp ctx.1 (List.ofFn r))
          ⟨⟨none, 0⟩, ctx.2⟩))
      else (setup G ℓ n1 n2 κ pp).bind fun ctx =>
        ((Prod.fst) <$> (simulate (freshRealHandler G n1 n2 A.budget PG κ pp ctx.1 ctx.2)
          (SAAdv.run G n1 n2 PG A κ pp ctx.1 (List.ofFn r)) ⟨none, 0⟩)) := rfl

/-- Actual raw simulation advantage compares the two fresh stateful endpoints
[Wee20, §3, p. 6, main claim with §3.3, pp. 7–8]. -/
noncomputable def freshSaSimAdv (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) : ℝ :=
  advantage (freshSaGame G n1 n2 PG A false κ) (freshSaGame G n1 n2 PG A true κ)

/-- The actual raw advantage is the shared advantage of the two fresh experiments. -/
theorem freshSaSimAdv_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) : freshSaSimAdv G n1 n2 PG A κ =
      advantage (freshSaGame G n1 n2 PG A false κ) (freshSaGame G n1 n2 PG A true κ) := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
