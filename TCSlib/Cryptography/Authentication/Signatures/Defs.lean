/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Authentication.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Digital signature schemes and forgery games

The forger is a non-uniform PPT machine. Its signing oracle logs queries through
`QueryImpl.withLog`, and forgery requires a fresh message and an accepting signature.

The formalization makes the following choices.

- **Fixed lengths.** Messages at parameter `n` are `ℓ(n)`-bit strings (the source's message space
  `{M_n}`), and signatures are `t(n)`-bit strings. An algorithm's output is read at its
  length by `padFin`. The oracle codec needs fixed lengths.
- **Algorithms.** `Gen` and `Sign` are uniform machines (PPTs), as in the ch. 2–4 layer's
  `PrivateKeyScheme`. `Ver` is a polynomial-time function, read as accepting on output `[true]`.
  Correctness holds for every coin string: the probability-one reading of the source.
- **Query budgets.** A forger's number of oracle queries is an explicit polynomial `q`, universally
  quantified in the security definitions, as in the ch. 2–4 layer's `OracleEnsemble.Indist`. The
  one-time notions fix the budget to one.
- **Signature forgers receive the public key.** The experiment displayed in Def 136.2 writes
  `A^{Sign_sk}(1^n)`; `Ver` is public, so the forger gets `pk` (the standard definition).

## Main definitions

* `SignatureScheme` specifies key generation, signing, verification and correctness.
* `SignatureScheme.forgeGame`, `SignatureScheme.Secure` and `SignatureScheme.OneTimeSecure`
  give the forgery experiment and its security predicates.

## Main results

The reading equations and predicate characterizations expose the signing oracle,
forgery experiment and security predicates.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definitions 135.1 and 136.2 and the one-time notion after Definition 136.2.
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Digital signatures -/

/-- A **digital signature scheme** over `ℓ(n)`-bit messages with `t(n)`-bit signatures
[PS10, Definition 135.1]: `Gen(1^n)` outputs `⟨pk, sk⟩`, `Sign_sk(m)` is activated on `⟨sk, m⟩`,
and a deterministic polynomial-time `Ver` on `⟨1^n, ⟨pk, ⟨m, σ⟩⟩⟩`, with perfect correctness. -/
structure SignatureScheme where
  /-- The message length `ℓ(n)`. -/
  msgLen : PolyExpr
  /-- The signature length `t(n)`. -/
  sigLen : PolyExpr
  /-- The key generator `Gen(1^n)`, with output `⟨pk, sk⟩`. -/
  gen : NUPPT
  /-- The signing algorithm `Sign_sk(m)`. -/
  sign : NUPPT
  /-- The verification algorithm; `[true]` is "accept". -/
  ver : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Sign` is a PPT. -/
  sign_uniform : sign.Uniform
  /-- `Ver` is deterministic polynomial-time. -/
  ver_poly : PolyTimeComputable ver
  /-- Perfect correctness, for every coin string [PS10, Definition 135.1]. -/
  correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (rs : sign.Coins n),
    ver (atParam n (pairEncode (pairFstD (gen.runAt n [] rg)) (pairEncode (List.ofFn m)
      (List.ofFn (padFin (sigLen.eval n) (sign.runAt n (pairEncode (pairSndD (gen.runAt n [] rg))
        (List.ofFn m)) rs)))))) = [true]

namespace SignatureScheme

variable (S : SignatureScheme)

/-- `Ver_pk(m, σ)` accepts. -/
def Accepts (n : ℕ) (pk : List Bool) (m : Fin (S.msgLen.eval n) → Bool)
    (σ : Fin (S.sigLen.eval n) → Bool) : Prop :=
  S.ver (atParam n (pairEncode pk (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true]

/-- A signature is accepted exactly when verification on `⟨1^n, ⟨pk, ⟨m, σ⟩⟩⟩` returns
`[true]` [PS10, Definition 135.1]. -/
theorem accepts_iff (n : ℕ) (pk : List Bool) (m : Fin (S.msgLen.eval n) → Bool)
    (σ : Fin (S.sigLen.eval n) → Bool) :
    S.Accepts n pk m σ ↔
      S.ver (atParam n (pairEncode pk (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true] :=
  Iff.rfl

instance (n : ℕ) (pk : List Bool) (m : Fin (S.msgLen.eval n) → Bool)
    (σ : Fin (S.sigLen.eval n) → Bool) : Decidable (S.Accepts n pk m σ) :=
  inferInstanceAs (Decidable (_ = _))

/-- The one signing oracle at parameter `n`. -/
abbrev oracleSpec (n : ℕ) : OracleSpec (Fin 1) :=
  bitSpec (fun _ => S.msgLen.eval n) (fun _ => S.sigLen.eval n)

/-- The signing oracle has message-length queries and signature-length answers:
`oracleSpec n = bitSpec (fun _ => msgLen(n)) (fun _ => sigLen(n))`. -/
theorem oracleSpec_eq (n : ℕ) :
    S.oracleSpec n = bitSpec (fun _ => S.msgLen.eval n) (fun _ => S.sigLen.eval n) := rfl

/-- The **signing oracle** `Sign_sk(·)`: each query `m` is answered by `Sign_sk(m)` with fresh
coins. -/
noncomputable def signImpl (n : ℕ) (sk : List Bool) : QueryImpl (S.oracleSpec n) Unit unifSpec :=
  QueryImpl.ofComp fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
    .pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs))

/-- The signing implementation samples fresh signing coins and returns the signature padded
to its declared length, using `QueryImpl.ofComp` [PS10, Definition 136.2]. -/
theorem signImpl_eq (n : ℕ) (sk : List Bool) :
    S.signImpl n sk =
      QueryImpl.ofComp (fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
        .pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs))) :=
  rfl

/-- The codec of forgers: one oracle, and a final output of `ℓ(n) + t(n)` bits read as `(m, σ)`. -/
def forgerCodec (n : ℕ) :
    MachineCodec (S.oracleSpec n) (Fin (S.msgLen.eval n + S.sigLen.eval n) → Bool) :=
  bitCodec (fun _ => S.msgLen.eval n) (fun _ => S.sigLen.eval n) (S.msgLen.eval n + S.sigLen.eval n)

/-- The signature forger codec decodes moves with `decodeBitMove` at message and signature
lengths. -/
theorem forgerCodec_decodeMove (n : ℕ) (w : List Bool) :
    (S.forgerCodec n).decodeMove w =
      decodeBitMove (fun _ => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
        (S.msgLen.eval n + S.sigLen.eval n) w :=
  bitCodec_decodeMove (fun _ => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
    (S.msgLen.eval n + S.sigLen.eval n) w

/-- The signature forger codec encodes a log entry `(i, m, σ)` as `⟨1^i, ⟨m, σ⟩⟩`. -/
theorem forgerCodec_encodeEntry (n : ℕ)
    (e : Σ i, (S.oracleSpec n).dom i × (S.oracleSpec n).rng i) :
    (S.forgerCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (fun _ => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
    (S.msgLen.eval n + S.sigLen.eval n) e

/-- When its query budget expires, the signature forger codec returns
`zeroBits (msgLen(n) + sigLen(n))`. -/
theorem forgerCodec_timeout (n : ℕ) :
    (S.forgerCodec n).timeout = zeroBits (S.msgLen.eval n + S.sigLen.eval n) :=
  bitCodec_timeout (fun _ => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
    (S.msgLen.eval n + S.sigLen.eval n)

/-- **The signature forgery game** [PS10, Definition 136.2] at parameter `n`, for the forger `A`
with query budget `b`: sample `⟨pk, sk⟩ ← Gen(1^n)` and `A`'s coins, run `A` on `pk` against the
logged signing oracle, and win when `A`'s output `(m, σ)` is accepted under `pk` and `m` was not
queried. -/
noncomputable def forgeGame (A : NUPPT) (b n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.signImpl n (pairSndD (S.gen.runAt n [] rg))).withLog
      (A.toCompOn (S.forgerCodec n) n b (pairFstD (S.gen.runAt n [] rg)) r) ((), [])).bind
    fun res =>
    .pure (decide
      (S.Accepts n (pairFstD (S.gen.runAt n [] rg)) (splitBits res.1).1 (splitBits res.1).2 ∧
        ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1))

/-- The signature forgery game samples the keys and forger coins, runs the forger on the public
key against the logged signing oracle, and tests acceptance and freshness
[PS10, Definition 136.2]. -/
theorem forgeGame_eq (A : NUPPT) (b n : ℕ) :
    S.forgeGame A b n =
      (ProbComp.sample (S.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.signImpl n (pairSndD (S.gen.runAt n [] rg))).withLog
          (A.toCompOn (S.forgerCodec n) n b (pairFstD (S.gen.runAt n [] rg)) r) ((), [])).bind
        fun res =>
        .pure (decide
          (S.Accepts n (pairFstD (S.gen.runAt n [] rg)) (splitBits res.1).1 (splitBits res.1).2 ∧
            ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1))) := rfl

/-- **A secure signature scheme** [PS10, Definition 136.2]: for every non-uniform PPT forger and
every polynomial query budget, the forgery probability is negligible. -/
def Secure : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, accept (S.forgeGame A (q.eval n) n) ≤ ε n

/-- A signature scheme is secure exactly when every machine and polynomial query budget have
a negligible upper bound on forgery acceptance [PS10, Definition 136.2]. -/
theorem secure_iff :
    S.Secure ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, accept (S.forgeGame A (q.eval n) n) ≤ ε n := Iff.rfl

/-- **A one-time secure signature scheme** [PS10, the notion after Definition 136.2]: Def 136.2
for forgers that may query the signing oracle once. -/
def OneTimeSecure : Prop :=
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, accept (S.forgeGame A 1 n) ≤ ε n

/-- A signature scheme is one-time secure exactly when every machine has a negligible upper
bound on forgery acceptance with one signing query [PS10, the notion after Definition 136.2]. -/
theorem oneTimeSecure_iff :
    S.OneTimeSecure ↔ ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, accept (S.forgeGame A 1 n) ≤ ε n := Iff.rfl

end SignatureScheme

end TCSlib.Cryptography.Authentication
