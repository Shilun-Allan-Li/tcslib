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
# Message authentication codes and their forgery game

## Main definitions

`MAC` gives the fixed-width scheme interface with uniform key generation and tagging,
polynomial-time verification, and perfect correctness for every coin string. At parameter
`n`, messages and tags have lengths given by the scheme's polynomials, and tagging output is
read with `padFin`.

`MAC.forgeGame` runs a machine against a logged tagging oracle. A forgery succeeds when
verification accepts the output and the message is fresh. `MAC.Secure` bounds the forgery
probability by a negligible function for each non-uniform PPT forger and polynomial query
budget.

## Main results

`MAC.forgeGame_eq` exposes the experiment. `MAC.secure_iff` states its security bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definitions 134.1 and 134.2.
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- A **message authentication code** over `ℓ(n)`-bit messages with `t(n)`-bit tags
[PS10, Definition 134.1]: a key generator `Gen(1^n)`, a tagging algorithm `Tag_k(m)` (activated on
`⟨k, m⟩`, its output read as `t(n)` bits), and a deterministic polynomial-time `Ver` on
`⟨1^n, ⟨k, ⟨m, σ⟩⟩⟩`, with perfect correctness. -/
structure MAC where
  /-- The message length `ℓ(n)`. -/
  msgLen : PolyExpr
  /-- The tag length `t(n)`. -/
  tagLen : PolyExpr
  /-- The key generator `Gen(1^n)`. -/
  gen : NUPPT
  /-- The tagging algorithm `Tag_k(m)`. -/
  tag : NUPPT
  /-- The verification algorithm; `[true]` is "accept". -/
  ver : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Tag` is a PPT. -/
  tag_uniform : tag.Uniform
  /-- `Ver` is deterministic polynomial-time. -/
  ver_poly : PolyTimeComputable ver
  /-- Perfect correctness, for every coin string [PS10, Definition 134.1 (4)]. -/
  correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (rt : tag.Coins n),
    ver (atParam n (pairEncode (gen.runAt n [] rg) (pairEncode (List.ofFn m)
      (List.ofFn (padFin (tagLen.eval n) (tag.runAt n (pairEncode (gen.runAt n [] rg)
        (List.ofFn m)) rt)))))) = [true]

namespace MAC

variable (M : MAC)

/-- `Ver_k(m, σ)` accepts. -/
def Accepts (n : ℕ) (k : List Bool) (m : Fin (M.msgLen.eval n) → Bool)
    (σ : Fin (M.tagLen.eval n) → Bool) : Prop :=
  M.ver (atParam n (pairEncode k (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true]

/-- A MAC accepts `(m, σ)` exactly when its verifier on `⟨1^n, ⟨k, ⟨m, σ⟩⟩⟩` returns
`[true]` [PS10, Definition 134.1]. -/
theorem accepts_iff (n : ℕ) (k : List Bool) (m : Fin (M.msgLen.eval n) → Bool)
    (σ : Fin (M.tagLen.eval n) → Bool) :
    M.Accepts n k m σ ↔
      M.ver (atParam n (pairEncode k (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true] :=
  Iff.rfl

instance (n : ℕ) (k : List Bool) (m : Fin (M.msgLen.eval n) → Bool)
    (σ : Fin (M.tagLen.eval n) → Bool) : Decidable (M.Accepts n k m σ) :=
  inferInstanceAs (Decidable (_ = _))

/-- The one tagging oracle at parameter `n`. -/
abbrev oracleSpec (n : ℕ) : OracleSpec (Fin 1) :=
  bitSpec (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n)

/-- The tagging oracle has message-length queries and tag-length answers:
`oracleSpec n = bitSpec (fun _ => msgLen(n)) (fun _ => tagLen(n))`. -/
theorem oracleSpec_eq (n : ℕ) :
    M.oracleSpec n = bitSpec (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n) := rfl

/-- The **tagging oracle** `Tag_k(·)`: each query `m` is answered by `Tag_k(m)` with fresh coins. -/
noncomputable def tagImpl (n : ℕ) (k : List Bool) : QueryImpl (M.oracleSpec n) Unit unifSpec :=
  QueryImpl.ofComp fun _ m => (ProbComp.sample (M.tag.Coins n)).bind fun rt =>
    .pure (padFin (M.tagLen.eval n) (M.tag.runAt n (pairEncode k (List.ofFn m)) rt))

/-- The tagging implementation samples fresh tag coins and returns the tag padded to its
declared length, using `QueryImpl.ofComp` [PS10, Definition 134.2]. -/
theorem tagImpl_eq (n : ℕ) (k : List Bool) :
    M.tagImpl n k =
      QueryImpl.ofComp (fun _ m => (ProbComp.sample (M.tag.Coins n)).bind fun rt =>
        .pure (padFin (M.tagLen.eval n) (M.tag.runAt n (pairEncode k (List.ofFn m)) rt))) :=
  rfl

/-- The codec of forgers: one oracle, and a final output of `ℓ(n) + t(n)` bits read as `(m, σ)`. -/
def forgerCodec (n : ℕ) :
    MachineCodec (M.oracleSpec n) (Fin (M.msgLen.eval n + M.tagLen.eval n) → Bool) :=
  bitCodec (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n)

/-- The MAC forger codec decodes moves with `decodeBitMove` at message and tag lengths. -/
theorem forgerCodec_decodeMove (n : ℕ) (w : List Bool) :
    (M.forgerCodec n).decodeMove w =
      decodeBitMove (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n)
        (M.msgLen.eval n + M.tagLen.eval n) w :=
  bitCodec_decodeMove (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n)
    (M.msgLen.eval n + M.tagLen.eval n) w

/-- The MAC forger codec encodes a log entry `(i, m, σ)` as `⟨1^i, ⟨m, σ⟩⟩`. -/
theorem forgerCodec_encodeEntry (n : ℕ)
    (e : Σ i, (M.oracleSpec n).dom i × (M.oracleSpec n).rng i) :
    (M.forgerCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n)
    (M.msgLen.eval n + M.tagLen.eval n) e

/-- When its query budget expires, the MAC forger codec returns `zeroBits (msgLen(n) +
tagLen(n))`. -/
theorem forgerCodec_timeout (n : ℕ) :
    (M.forgerCodec n).timeout = zeroBits (M.msgLen.eval n + M.tagLen.eval n) :=
  bitCodec_timeout (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n)
    (M.msgLen.eval n + M.tagLen.eval n)

/-- **The MAC forgery game** [PS10, Definition 134.2] at parameter `n`, for the forger `A` with
query budget `b`: sample a key `k ← Gen(1^n)` and `A`'s coins, run `A` against the logged tagging
oracle, and win when `A`'s output `(m, σ)` is accepted and `m` was not queried. -/
noncomputable def forgeGame (A : NUPPT) (b n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (M.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (M.tagImpl n (M.gen.runAt n [] rg)).withLog (A.toComp (M.forgerCodec n) n b r)
      ((), [])).bind fun res =>
    .pure (decide (M.Accepts n (M.gen.runAt n [] rg) (splitBits res.1).1 (splitBits res.1).2 ∧
      ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1))

/-- The MAC forgery game samples the key and forger coins, runs the logged tagging oracle,
and tests acceptance and message freshness [PS10, Definition 134.2]. -/
theorem forgeGame_eq (A : NUPPT) (b n : ℕ) :
    M.forgeGame A b n =
      (ProbComp.sample (M.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (M.tagImpl n (M.gen.runAt n [] rg)).withLog (A.toComp (M.forgerCodec n) n b r)
          ((), [])).bind fun res =>
        .pure (decide (M.Accepts n (M.gen.runAt n [] rg) (splitBits res.1).1 (splitBits res.1).2 ∧
          ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1))) := rfl

/-- **A secure MAC** [PS10, Definition 134.2]: for every non-uniform PPT forger and every
polynomial query budget, the forgery probability is negligible. -/
def Secure : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, accept (M.forgeGame A (q.eval n) n) ≤ ε n

/-- A MAC is secure exactly when every machine and polynomial query budget have a negligible
upper bound on forgery acceptance [PS10, Definition 134.2]. -/
theorem secure_iff :
    M.Secure ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, accept (M.forgeGame A (q.eval n) n) ≤ ε n := Iff.rfl

end MAC

end TCSlib.Cryptography.Authentication
