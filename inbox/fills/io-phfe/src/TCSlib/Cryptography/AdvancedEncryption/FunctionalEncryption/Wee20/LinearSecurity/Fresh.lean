/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fresh-draw semi-adaptive experiments for the linear building block

## Main definitions

* `Wee20.Linear.freshRealHandler`: actual `enc` and `keyGen` at each accepted query.
* `Wee20.Linear.freshIdealHandler`: actual `simEnc` and `simKey` at each accepted query.
* `Wee20.Linear.freshSaGame`, `freshSaSimAdv`: setup followed by the stateful interaction.

## Main results

Equation readers expose all fresh core-plus-draw calls. `LinearSecurity.Endpoint` proves
that these experiments have the same acceptance laws as the padded unfiltered endpoints.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §2.2, p. 5 and §4.2,
  pp. 9–10. The total call budget includes the challenge, and the key matrix is group-valued.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

/-- The real oracle calls the actual honest laws with fresh randomness at each accepted
query [Wee20, §2.2, p. 5; §4.2, p. 9]. Refusals sample nothing and preserve state. -/
noncomputable def freshRealHandler (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr)
    (κ : ℕ) (pp : PublicParams G κ) (pk : MPK G ℓ zDim κ pp)
    (msk : MSK G ℓ zDim κ pp) :
    QueryImpl (saSpec G PG zDim κ pp) (SAState G ℓ zDim κ pp) unifSpec
  | false, msg, st => match st.challenge with
    | none => ((fun ct => (some ct, ⟨some msg, st.used⟩)) <$> (enc G ℓ zDim κ pp pk msg.1
      (pp.group.expVec pp.generator msg.2)))
    | some _ => .pure (none, st)
  | true, query, st => match st.challenge with
    | none => .pure (none, st)
    | some _ => if st.used < q.eval κ then
        ((fun key => (some ⟨query.fn, key⟩, ⟨st.challenge, st.used + 1⟩)) <$> (keyGen G PG zDim κ pp
          msk query.fn query.matrix))
      else .pure (none, st)

/-- The fresh real challenge law encrypts its scalar private input in the source group. -/
theorem freshRealHandler_challenge (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr)
    (κ : ℕ) (pp : PublicParams G κ) (pk : MPK G ℓ zDim κ pp)
    (msk : MSK G ℓ zDim κ pp) (msg : Challenge G ℓ zDim κ pp)
    (st : SAState G ℓ zDim κ pp) :
    freshRealHandler G PG zDim q κ pp pk msk false msg st =
      match st.challenge with
      | none => ((fun ct => (some ct, ⟨some msg, st.used⟩)) <$> (enc G ℓ zDim κ pp pk msg.1
        (pp.group.expVec pp.generator msg.2)))
      | some _ => .pure (none, st) := rfl

/-- The fresh real key law samples its actual function-dependent draw after acceptance. -/
theorem freshRealHandler_key (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr)
    (κ : ℕ) (pp : PublicParams G κ) (pk : MPK G ℓ zDim κ pp)
    (msk : MSK G ℓ zDim κ pp) (query : KeyQuery G PG zDim κ pp)
    (st : SAState G ℓ zDim κ pp) :
    freshRealHandler G PG zDim q κ pp pk msk true query st =
      match st.challenge with
      | none => .pure (none, st)
      | some _ => if st.used < q.eval κ then
          ((fun key => (some ⟨query.fn, key⟩, ⟨st.challenge, st.used + 1⟩)) <$> (keyGen G PG zDim κ
            pp msk query.fn query.matrix))
        else .pure (none, st) := rfl

/-- The ideal oracle calls the actual simulator laws at each accepted query
[Wee20, §2.2, p. 5; §4.2, p. 10]. Its setup state persists, and the protocol state retains
x,z so every later key receives precisely its allowed source-group leakage. -/
noncomputable def freshIdealHandler (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr)
    (κ : ℕ) (pp : PublicParams G κ) (sim : SimState G ℓ zDim κ pp) :
    QueryImpl (saSpec G PG zDim κ pp) (SAState G ℓ zDim κ pp) unifSpec
  | false, msg, st => match st.challenge with
    | none => ((fun ct => (some ct, ⟨some msg, st.used⟩)) <$> (simEnc G ℓ zDim κ pp sim msg.1))
    | some _ => .pure (none, st)
  | true, query, st => match st.challenge with
    | none => .pure (none, st)
    | some msg => if st.used < q.eval κ then
        ((fun key => (some ⟨query.fn, key⟩, ⟨st.challenge, st.used + 1⟩)) <$> (simKey G PG zDim κ pp
          sim query.fn query.matrix msg.1
          (leak G PG zDim κ pp query.fn query.matrix msg.1 msg.2)))
      else .pure (none, st)

/-- The fresh ideal ciphertext law is the actual simulator encryption law. -/
theorem freshIdealHandler_challenge (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr)
    (κ : ℕ) (pp : PublicParams G κ) (sim : SimState G ℓ zDim κ pp)
    (msg : Challenge G ℓ zDim κ pp) (st : SAState G ℓ zDim κ pp) :
    freshIdealHandler G PG zDim q κ pp sim false msg st =
      match st.challenge with
      | none => ((fun ct => (some ct, ⟨some msg, st.used⟩)) <$> (simEnc G ℓ zDim κ pp sim msg.1))
      | some _ => .pure (none, st) := rfl

/-- The fresh ideal key law uses the supplied matrix and its exact scalar-input leakage. -/
theorem freshIdealHandler_key (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr)
    (κ : ℕ) (pp : PublicParams G κ) (sim : SimState G ℓ zDim κ pp)
    (query : KeyQuery G PG zDim κ pp) (st : SAState G ℓ zDim κ pp) :
    freshIdealHandler G PG zDim q κ pp sim true query st =
      match st.challenge with
      | none => .pure (none, st)
      | some msg => if st.used < q.eval κ then
          ((fun key => (some ⟨query.fn, key⟩, ⟨st.challenge, st.used + 1⟩)) <$> (simKey G PG zDim κ
            pp sim query.fn query.matrix msg.1
            (leak G PG zDim κ pp query.fn query.matrix msg.1 msg.2)))
        else .pure (none, st) := rfl

/-- The raw semi-adaptive experiment samples the ACTUAL setup law and invokes the ACTUAL
fresh encryption/key laws through the shared stateful simulator
[Wee20, §2.2, p. 5; §4.2, pp. 9–10]. No basis filter is applied at either endpoint. -/
noncomputable def freshSaGame (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr)
    (A : SAAdv G PG zDim) (ideal : Bool) (κ : ℕ) : ProbComp Bool :=
  (publicParamsGen G κ).bind fun pp =>
  (ProbComp.sample (Fin (A.coins.eval κ) → Bool)).bind fun r =>
  if ideal then (simSetup G ℓ zDim κ pp).bind fun ctx =>
    ((Prod.fst) <$> (simulate (freshIdealHandler G PG zDim A.budget κ pp ctx.2)
      (SAAdv.run G PG zDim A κ pp ctx.1 (List.ofFn r)) ⟨none, 0⟩))
  else (setup G ℓ zDim κ pp).bind fun ctx =>
    ((Prod.fst) <$> (simulate (freshRealHandler G PG zDim A.budget κ pp ctx.1 ctx.2)
      (SAAdv.run G PG zDim A κ pp ctx.1 (List.ofFn r)) ⟨none, 0⟩))

/-- The fresh experiment is the displayed setup and stateful simulation of its raw laws. -/
theorem freshSaGame_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim)
    (ideal : Bool) (κ : ℕ) :
    freshSaGame G PG zDim A ideal κ =
      (publicParamsGen G κ).bind fun pp =>
      (ProbComp.sample (Fin (A.coins.eval κ) → Bool)).bind fun r =>
      if ideal then (simSetup G ℓ zDim κ pp).bind fun ctx =>
        ((Prod.fst) <$> (simulate (freshIdealHandler G PG zDim A.budget κ pp ctx.2)
          (SAAdv.run G PG zDim A κ pp ctx.1 (List.ofFn r)) ⟨none, 0⟩))
      else (setup G ℓ zDim κ pp).bind fun ctx =>
        ((Prod.fst) <$> (simulate (freshRealHandler G PG zDim A.budget κ pp ctx.1 ctx.2)
          (SAAdv.run G PG zDim A κ pp ctx.1 (List.ofFn r)) ⟨none, 0⟩)) := rfl

/-- Fresh-law simulation advantage compares the actual raw endpoints
[Wee20, Appendix B, Theorem 1, p. 12 and §2.2, p. 5]. -/
noncomputable def freshSaSimAdv (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr)
    (A : SAAdv G PG zDim) (κ : ℕ) : ℝ :=
  advantage (freshSaGame G PG zDim A false κ) (freshSaGame G PG zDim A true κ)

/-- Fresh-law advantage is the library advantage between the displayed raw experiments. -/
theorem freshSaSimAdv_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim) (κ : ℕ) :
    freshSaSimAdv G PG zDim A κ =
      advantage (freshSaGame G PG zDim A false κ) (freshSaGame G PG zDim A true κ) := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
