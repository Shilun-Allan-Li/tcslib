/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuerySampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A common transcript for the hash-and-sign reductions

Fix the signature keys, hash index, adversary tape and signing tape. The resulting
transcript is shared by the collision-finding and signature-forging reductions of
[PS10, Theorem 144.1]. Because the adversary makes at most one query, sampling signing
coins per query has the same law as drawing the signing tape before this transcript.

## Main definitions

* `HashSignFill.hashedReply`: the original signer applied to the hashed message.
* `HashSignFill.fixedSign`, `sampledHashSign`: the fixed-tape and fresh-tape signing oracles.
* `HashSignFill.transcript`: the adversary's output and full signing-query log.
* `HashSignFill.Success`: acceptance and message freshness in a common transcript.

## Main results

* The defining equations and application readers expose each computation.
* `HashSignFill.expect_sampledHashSign_eq_transcript`: signing randomness may be sampled
  before the common transcript.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 144.1, book pp. 144–145.
-/

namespace TCSlib.Cryptography.Authentication.HashSignFill

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- With signing tape `rs` fixed, hash `m` and run the original signer under `sk`, padding
the signature to the declared signature width [PS10, Theorem 144.1]. -/
def hashedReply (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) (m : Fin (H.domLen.eval n) → Bool) :
    Fin (S.sigLen.eval n) → Bool :=
  padFin (S.sigLen.eval n) (S.sign.runAt n
    (pairEncode sk (HashSignForward.hashWord H S (List.replicate n true) i (List.ofFn m))) rs)

/-- The fixed-tape hashed reply is the padded original signer output on `⟨sk, h_i(m)⟩`. -/
theorem hashedReply_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) (m : Fin (H.domLen.eval n) → Bool) :
    hashedReply H S n sk i rs m =
      padFin (S.sigLen.eval n) (S.sign.runAt n
        (pairEncode sk (HashSignForward.hashWord H S (List.replicate n true) i (List.ofFn m)))
        rs) := rfl

/-- The fixed-tape signing oracle answers every query using `hashedReply` and has trivial
state [PS10, Theorem 144.1]. -/
def fixedSign (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) :
    QueryImpl (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n))
      Unit unifSpec :=
  fun _ m _ => .pure (hashedReply H S n sk i rs m, ())

/-- The fixed-tape oracle is the pure answer function `m ↦ (hashedReply m, ())`. -/
theorem fixedSign_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) :
    fixedSign H S n sk i rs = fun _ m _ => .pure (hashedReply H S n sk i rs m, ()) := rfl

/-- Applying the fixed-tape oracle returns the hashed signature and trivial state. -/
theorem fixedSign_apply (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (s : Unit) :
    fixedSign H S n sk i rs j m s = .pure (hashedReply H S n sk i rs m, ()) := rfl

/-- The common transcript runs `A` on `⟨pk,i⟩` with one query allowed, fixed signing tape,
and a full query log [PS10, Theorem 144.1]. -/
def transcript (H : CRH) (S : SignatureScheme) (A : NUPPT) (n : ℕ)
    (pk sk i : List Bool) (rs : S.sign.Coins n) (rA : A.Coins n) :
    ProbComp ((Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) :=
  simulate (fixedSign H S n sk i rs).withLog
    (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
      (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA) ((), [])

/-- The common transcript is the logged simulation with the fixed-tape signing oracle. -/
theorem transcript_eq (H : CRH) (S : SignatureScheme) (A : NUPPT) (n : ℕ)
    (pk sk i : List Bool) (rs : S.sign.Coins n) (rA : A.Coins n) :
    transcript H S A n pk sk i rs rA =
      simulate (fixedSign H S n sk i rs).withLog
        (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
          (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA) ((), []) := rfl

/-- The fresh-tape hash-and-sign oracle samples an original signing tape independently
for every query and keeps trivial state [PS10, Theorem 144.1]. -/
noncomputable def sampledHashSign (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool) :
    QueryImpl (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n))
      Unit unifSpec :=
  QueryImpl.ofComp fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
    .pure (hashedReply H S n sk i rs m)

/-- The fresh-tape oracle is `ofComp` of the original signing-tape sample followed by
the corresponding fixed-tape hashed reply. -/
theorem sampledHashSign_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool) :
    sampledHashSign H S n sk i =
      QueryImpl.ofComp (fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
        .pure (hashedReply H S n sk i rs m)) := rfl

/-- Applying the fresh-tape oracle samples one signing tape, returns its hashed signature,
and preserves the trivial state. -/
theorem sampledHashSign_apply (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (s : Unit) :
    sampledHashSign H S n sk i j m s =
      (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
        .pure (hashedReply H S n sk i rs m, s) := by
  simp only [sampledHashSign_eq, QueryImpl.ofComp_apply,
    OracleComp.bind_assoc, OracleComp.pure_bind]

/-- The expected payoff of a fresh-tape hash-and-sign simulation equals the expectation
obtained by drawing one signing tape and running the common transcript, including its log.

**Proof sketch.** The machine computation has unit query cost at most one by its published
budget contract. `expect_simulate_sample_once` therefore moves the signing-tape sample
outside the logged simulation; the fixed-tape implementation is exactly `fixedSign`. -/
theorem expect_sampledHashSign_eq_transcript (H : CRH) (S : SignatureScheme) (A : NUPPT)
    (n : ℕ) (pk sk i : List Bool) (rA : A.Coins n)
    (g : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n))) → ℝ) :
    ProbComp.expect
        (simulate (sampledHashSign H S n sk i).withLog
          (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
            (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA) ((), [])) g =
      ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
        ProbComp.expect (transcript H S A n pk sk i rs rA) g) := by
  simpa only [sampledHashSign_eq, transcript_eq, fixedSign_eq] using
    expect_simulate_sample_once (fun (_ : Fin 1) m rs => hashedReply H S n sk i rs m)
      (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
        (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA)
      (A.toCompOn_costBoundedBy _ n 1 (pairEncode pk i) rA) g

/-- The common transcript is a successful hash-and-sign forgery when the original verifier
accepts the hashed final message and that message did not occur in the inner query log
[PS10, Theorem 144.1]. -/
def Success (H : CRH) (S : SignatureScheme) (n : ℕ) (pk i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) : Prop :=
  S.Accepts n pk (padFin (S.msgLen.eval n)
      (H.eval (atParam n (pairEncode i (List.ofFn (splitBits res.1).1)))))
    (splitBits res.1).2 ∧
    ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1

/-- Success is original-scheme acceptance on the hash, together with freshness of the
unhashed final message in the common query log. -/
theorem success_iff (H : CRH) (S : SignatureScheme) (n : ℕ) (pk i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) :
    Success H S n pk i res ↔
      S.Accepts n pk (padFin (S.msgLen.eval n)
        (H.eval (atParam n (pairEncode i (List.ofFn (splitBits res.1).1)))))
        (splitBits res.1).2 ∧
      ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1 := Iff.rfl

end TCSlib.Cryptography.Authentication.HashSignFill
