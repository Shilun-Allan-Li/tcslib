/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The collision-finding handler for hash-and-sign

The non-interactive reduction in [PS10, Theorem 144.1] receives the hash index, samples
signature keys, and answers the sole signing query itself. Its state remembers that query;
the final output concatenates the query and the forged message for the CRH collision game.

## Main definitions

* `HashSignFill.collisionKey`, `collisionAdv`, `collisionHash`, `collisionRun`,
  `collisionOut`: the string computations of the reduction.
* `HashSignFill.collisionHandler`: their polynomial-time T1 handler.

## Main results

* The string equations and handler field equations expose every computation.
* `HashSignFill.exists_collisionMachine`: T1 realizes this handler as a machine.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 144.1, collision-finding case.
-/

namespace TCSlib.Cryptography.Authentication.HashSignFill

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The signature key word generated from the first `S.gen.coins(n)` bits of the
context seed, with empty argument and advice [PS10, Theorem 144.1]. -/
def collisionKey (S : SignatureScheme) (c : List Bool) : List Bool :=
  S.gen.output (NUPPT.layout (pairFstD c) [] []
    ((pairSndD (pairSndD c)).take (S.gen.coins.eval (pairFstD c).length)))

/-- `collisionKey S c` runs the original key generator on the parameter and the first
generator-sized segment of the context seed. -/
theorem collisionKey_eq (S : SignatureScheme) (c : List Bool) :
    collisionKey S c = S.gen.output (NUPPT.layout (pairFstD c) [] []
      ((pairSndD (pairSndD c)).take (S.gen.coins.eval (pairFstD c).length))) := rfl

/-- Generating the signature key from a context is polynomial-time. The tape segment is
computed by the published polynomial-length take construction. -/
theorem polyTimeComputable_collisionKey (S : SignatureScheme) :
    PolyTimeComputable (collisionKey S) :=
  let hW := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  let hT := ((polyTimeComputable_pairTakePoly S.gen.coins).comp'
    (polyTimeComputable_pairFstD.pairEncode hW)).congr (fun _ =>
      congrArg₂ (fun u w : List Bool => w.take (S.gen.coins.eval u.length))
        (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
  S.gen.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
    polyTimeComputable_pairFstD (polyTimeComputable_const [])
    (polyTimeComputable_const []) hT)

/-- When the context seed concatenates generator and signing tapes, `collisionKey` is
exactly the original generator's run on its own tape. -/
theorem collisionKey_seed (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (rg : S.gen.Coins n) (rs : S.sign.Coins n) :
    collisionKey S (seedIn n i (List.ofFn rg ++ List.ofFn rs)) = S.gen.runAt n [] rg := by
  simp only [collisionKey_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
  rw [← NUPPT.coinLen_eq S.gen n, List.take_left' List.length_ofFn,
    S.gen_uniform.runAt_eq, NUPPT.layout_eq, NUPPT.advInput_eq]

/-- The adversary receives `⟨pk, i⟩`, where the context supplies the hash index and
`collisionKey` supplies the public signature key [PS10, Theorem 144.1]. -/
def collisionAdv (S : SignatureScheme) (c : List Bool) : List Bool :=
  pairEncode (pairFstD (collisionKey S c)) (pairFstD (pairSndD c))

/-- The adversary input is the original public key paired with the context index. -/
theorem collisionAdv_eq (S : SignatureScheme) (c : List Bool) :
    collisionAdv S c =
      pairEncode (pairFstD (collisionKey S c)) (pairFstD (pairSndD c)) := rfl

/-- Pairing the generated public key with the index is polynomial-time. -/
theorem polyTimeComputable_collisionAdv (S : SignatureScheme) :
    PolyTimeComputable (collisionAdv S) :=
  (polyTimeComputable_pairFstD.comp' (polyTimeComputable_collisionKey S)).pairEncode
    (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD)

/-- At `seedIn n i ω`, the adversary input is `⟨pk, i⟩`, where the original generator
runs with the first `S.gen.coins(n)` seed bits. -/
theorem collisionAdv_seedIn (S : SignatureScheme) (n : ℕ) (i ω : List Bool) :
    collisionAdv S (seedIn n i ω) =
      pairEncode (pairFstD (S.gen.output (NUPPT.layout (List.replicate n true) [] []
        (ω.take (S.gen.coins.eval n))))) i := by
  simp only [collisionAdv_eq, collisionKey_eq, seedIn_eq, pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate]

/-- On concatenated generator and signing tapes, the adversary receives the public key
from that generator run paired with the supplied hash index. -/
theorem collisionAdv_seed (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (rg : S.gen.Coins n) (rs : S.sign.Coins n) :
    collisionAdv S (seedIn n i (List.ofFn rg ++ List.ofFn rs)) =
      pairEncode (pairFstD (S.gen.runAt n [] rg)) i := by
  rw [collisionAdv_eq, collisionKey_seed, seedIn_eq,
    pairSndD_pairEncode, pairFstD_pairEncode]

/-- The query hash in a handler-round word is the CRH evaluator padded to the signature
message length. The theorem's length hypothesis later identifies this with `H.hash`
[PS10, Theorem 144.1]. -/
def collisionHash (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
  padStr S.msgLen (pairFstD (pairFstD w))
    (H.eval (pairEncode (pairFstD (pairFstD w))
      (pairEncode (pairFstD (pairSndD (pairFstD w)))
        (pairSndD (pairSndD (pairSndD w))))))

/-- The query hash runs the evaluator at the context parameter and index on the query
word and pads its output to the signature message length. -/
theorem collisionHash_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
    collisionHash H S w = padStr S.msgLen (pairFstD (pairFstD w))
      (H.eval (pairEncode (pairFstD (pairFstD w))
        (pairEncode (pairFstD (pairSndD (pairFstD w)))
          (pairSndD (pairSndD (pairSndD w)))))) := rfl

/-- Evaluating and padding the query hash is polynomial-time by the CRH evaluator and
the published padding construction. -/
theorem polyTimeComputable_collisionHash (H : CRH) (S : SignatureScheme) :
    PolyTimeComputable (collisionHash H S) :=
  let hU := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
  let hI := polyTimeComputable_pairFstD.comp'
    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
  let hX := polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
  let hE := H.eval_poly.comp' (hU.pairEncode (hI.pairEncode hX))
  ((polyTimeComputable_padStr S.msgLen).comp' (hU.pairEncode hE)).congr (fun _ =>
    congrArg₂ (padStr S.msgLen) (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))

/-- A collision-finder round signs the query hash using the remaining seed and records
the query as its new state [PS10, Theorem 144.1]. -/
def collisionRun (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
  pairEncode
    (padStr S.sigLen (pairFstD (pairFstD w))
      (S.sign.output (NUPPT.layout (pairFstD (pairFstD w))
        (pairEncode (pairSndD (collisionKey S (pairFstD w))) (collisionHash H S w)) []
        ((pairSndD (pairSndD (pairFstD w))).drop
          (S.gen.coins.eval (pairFstD (pairFstD w)).length)))))
    (pairSndD (pairSndD (pairSndD w)))

/-- A round returns the padded original signature and the queried message. -/
theorem collisionRun_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
    collisionRun H S w = pairEncode
      (padStr S.sigLen (pairFstD (pairFstD w))
        (S.sign.output (NUPPT.layout (pairFstD (pairFstD w))
          (pairEncode (pairSndD (collisionKey S (pairFstD w))) (collisionHash H S w)) []
          ((pairSndD (pairSndD (pairFstD w))).drop
            (S.gen.coins.eval (pairFstD (pairFstD w)).length)))))
      (pairSndD (pairSndD (pairSndD w))) := rfl

/-- The collision-finder round is polynomial-time. It uses a polynomial-length coin
suffix, the polynomial-time signer and padding, then pairs the result with the query. -/
theorem polyTimeComputable_collisionRun (H : CRH) (S : SignatureScheme) :
    PolyTimeComputable (collisionRun H S) :=
  let hU := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
  let hW := polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
  let hR := ((polyTimeComputable_pairDropPoly S.gen.coins).comp'
    (hU.pairEncode hW)).congr (fun _ =>
      congrArg₂ (fun u r : List Bool => r.drop (S.gen.coins.eval u.length))
        (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
  let hK := polyTimeComputable_pairSndD.comp'
    ((polyTimeComputable_collisionKey S).comp' polyTimeComputable_pairFstD)
  let hSig := S.sign.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU
    (hK.pairEncode (polyTimeComputable_collisionHash H S)) (polyTimeComputable_const []) hR)
  let hPad := ((polyTimeComputable_padStr S.sigLen).comp' (hU.pairEncode hSig)).congr
    (fun _ => congrArg₂ (padStr S.sigLen)
      (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
  hPad.pairEncode (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD))

/-- The collision output concatenates the remembered query with the first `H.domLen(n)`
bits of the adversary's final word [PS10, Theorem 144.1]. -/
def collisionOut (H : CRH) (w : List Bool) : List Bool :=
  pairFstD (pairSndD w) ++
    (pairSndD (pairSndD w)).take (H.domLen.eval (pairFstD (pairFstD w)).length)

/-- The collision output is the state followed by the message prefix of the forgery. -/
theorem collisionOut_eq (H : CRH) (w : List Bool) :
    collisionOut H w = pairFstD (pairSndD w) ++
      (pairSndD (pairSndD w)).take (H.domLen.eval (pairFstD (pairFstD w)).length) := rfl

/-- Reading a polynomial-length forgery prefix and appending it to the stored query is
polynomial-time. -/
theorem polyTimeComputable_collisionOut (H : CRH) :
    PolyTimeComputable (collisionOut H) :=
  let hU := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
  let hA := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  let hT := ((polyTimeComputable_pairTakePoly H.domLen).comp' (hU.pairEncode hA)).congr
    (fun _ => congrArg₂ (fun u a : List Bool => a.take (H.domLen.eval u.length))
      (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
  (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD).append hT

/-- The T1 collision finder samples signature-generation and signing coins, remembers one
domain-width query, and emits the query followed by the forged message [PS10, Theorem 144.1]. -/
def collisionHandler (H : CRH) (S : SignatureScheme) :
    PolyHandler 1 (fun _ => H.domLen) (fun _ => S.sigLen) where
  stateLen := H.domLen
  seedLen := .add S.gen.coins S.sign.coins
  init _ := zeroBits _
  run := collisionRun H S
  poly := polyTimeComputable_collisionRun H S
  advIn := collisionAdv S
  advIn_poly := polyTimeComputable_collisionAdv S
  out := collisionOut H
  out_poly := polyTimeComputable_collisionOut H

attribute [simps (config := { isSimp := false }) stateLen seedLen init run advIn out]
  collisionHandler

/-- On a well-formed round input, the collision handler returns the padded signature on
the query hash and stores exactly the query. The generator reads the seed prefix and
the signer reads its suffix; the old state and oracle index are ignored. -/
theorem collisionHandler_run_input (H : CRH) (S : SignatureScheme) (n : ℕ)
    (i ω s : List Bool) (j : Fin 1) (m : List Bool) :
    (collisionHandler H S).run (PolyHandler.input n i ω s j m) =
      pairEncode
        (padStr S.sigLen (List.replicate n true)
          (S.sign.output (NUPPT.layout (List.replicate n true)
            (pairEncode
              (pairSndD (collisionKey S (seedIn n i ω)))
              (padStr S.msgLen (List.replicate n true)
                (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
            (ω.drop (S.gen.coins.eval n))))) m := by
  simp only [collisionHandler_run, collisionRun_eq, collisionHash_eq, PolyHandler.input_eq,
    seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- The typed signature returned by the collision handler: run the original signer on the
hashed message with the seed suffix and pad its output to `S.sigLen(n)` bits. -/
def collisionReply (H : CRH) (S : SignatureScheme) (n : ℕ) (i ω m : List Bool) :
    Fin (S.sigLen.eval n) → Bool :=
  padFin (S.sigLen.eval n)
    (S.sign.output (NUPPT.layout (List.replicate n true)
      (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
        (padStr S.msgLen (List.replicate n true)
          (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
      (ω.drop (S.gen.coins.eval n))))

/-- The typed reply is the original signer output padded to the signature length. -/
theorem collisionReply_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (i ω m : List Bool) :
    collisionReply H S n i ω m = padFin (S.sigLen.eval n)
      (S.sign.output (NUPPT.layout (List.replicate n true)
        (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
          (padStr S.msgLen (List.replicate n true)
            (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
        (ω.drop (S.gen.coins.eval n)))) := rfl

/-- With the generator and signing tapes concatenated into the context seed, the collision
handler's reply is the fixed experiment's hashed reply under those same generated keys. -/
theorem collisionReply_seed (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (rg : S.gen.Coins n) (rs : S.sign.Coins n) (m : Fin (H.domLen.eval n) → Bool) :
    collisionReply H S n i (List.ofFn rg ++ List.ofFn rs) (List.ofFn m) =
      hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m := by
  rw [collisionReply_eq, collisionKey_seed, hashedReply_eq,
    ← NUPPT.coinLen_eq S.gen n, List.drop_left' List.length_ofFn,
    S.sign_uniform.runAt_eq, HashSignForward.hashWord_eq,
    NUPPT.layout_eq, NUPPT.advInput_eq]

/-- Encoding the typed reply gives exactly the padded signature word emitted by a
collision-handler round. -/
theorem ofFn_collisionReply (H : CRH) (S : SignatureScheme) (n : ℕ) (i ω m : List Bool) :
    List.ofFn (collisionReply H S n i ω m) =
      padStr S.sigLen (List.replicate n true)
        (S.sign.output (NUPPT.layout (List.replicate n true)
          (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
            (padStr S.msgLen (List.replicate n true)
              (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
          (ω.drop (S.gen.coins.eval n)))) := by
  rw [collisionReply_eq]
  simpa only [List.length_replicate] using
    ofFn_padFin_eq_padStr S.sigLen (List.replicate n true) _

/-- The collision handler answers each typed query with its padded original signature and
sets the state to that query, asking no further oracle. -/
theorem collisionHandler_impl (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool) (j : Fin 1)
    (m s : Fin (H.domLen.eval n) → Bool) :
    (collisionHandler H S).impl n i ω j m s =
      .pure (collisionReply H S n i (List.ofFn ω) (List.ofFn m), m) := by
  rw [PolyHandler.impl_apply]
  congr 1
  apply PolyHandler.answer_of_run_eq
  rw [collisionHandler_run_input, ofFn_collisionReply]

/-- Finalization returns the remembered query followed by the domain-width message prefix
of the adversary's output. -/
theorem collisionHandler_result (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
    (s : Fin (H.domLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool) :
    (collisionHandler H S).result n i ω s a =
      List.ofFn s ++ (List.ofFn a).take (H.domLen.eval n) := by
  simp only [PolyHandler.result_eq, collisionHandler_out, collisionOut_eq, seedIn_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- The collision handler and common fixed-tape transcript return the same adversary
output. Their query log is empty, or consists of one query which is exactly the handler's
final state, answered by the same original signing tape.

**Proof sketch.** The adversary's computation has at most one query. If it returns
immediately, both simulations return that value and the transcript log is empty. Otherwise,
the seed equations identify the handler's response with the fixed experiment's response;
the handler stores the query while the fixed experiment logs it. Both continuations
therefore return the same function of that response. -/
theorem collisionHandler_transcript (H : CRH) (S : SignatureScheme) (A : NUPPT) (n : ℕ)
    (i : List Bool) (rg : S.gen.Coins n) (rs : S.sign.Coins n) (rA : A.Coins n)
    (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
    (hω : List.ofFn ω = List.ofFn rg ++ List.ofFn rs) :
    ∃ (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
      (s : Fin (H.domLen.eval n) → Bool)
      (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n))),
      simulate ((collisionHandler H S).impl n i ω)
          (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n)
            (fun _ => S.sigLen.eval n) (H.domLen.eval n + S.sigLen.eval n)) n 1
            ((collisionHandler H S).advInput n i ω) rA) ((collisionHandler H S).init n) =
          .pure (a, s) ∧
        transcript H S A n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) i rs rA = .pure (a, ((), L)) ∧
        (L = [] ∨ ∃ (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool),
          L = [⟨j, m, hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m⟩] ∧ s = m) := by
  have hinput : (collisionHandler H S).advInput n i ω =
      pairEncode (pairFstD (S.gen.runAt n [] rg)) i := by
    rw [PolyHandler.advInput_eq, collisionHandler_advIn, hω, collisionAdv_seed]
  let c := A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n)
    (fun _ => S.sigLen.eval n) (H.domLen.eval n + S.sigLen.eval n)) n 1
    (pairEncode (pairFstD (S.gen.runAt n [] rg)) i) rA
  have hc : c.CostBoundedBy (fun _ => 1) 1 := A.toCompOn_costBoundedBy _ n 1 _ rA
  rcases one_query_cases c hc with ⟨a, hcase⟩ | ⟨j, m, f, hcase⟩
  all_goals dsimp only [c] at hcase
  · refine ⟨a, (collisionHandler H S).init n, [], ?_, ?_, Or.inl rfl⟩
    · rw [hinput, hcase, simulate_pure]
    · rw [transcript_eq, hcase, simulate_pure]
  · let y := hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m
    refine ⟨f y, m, [⟨j, m, y⟩], ?_, ?_, Or.inr ⟨j, m, rfl, rfl⟩⟩
    · rw [hinput, hcase, simulate_query, collisionHandler_impl, hω, collisionReply_seed,
        OracleComp.pure_bind, simulate_pure]
    · rw [transcript_eq, hcase]
      simp only [simulate_query, QueryImpl.withLog_apply, fixedSign_apply,
        OracleComp.pure_bind, simulate_pure, List.nil_append]
      rfl

/-- If the common transcript is fresh and contains a query with the forged message's
hash, the collision handler's final output satisfies the CRH game's exact collision
predicate on the full domain [PS10, Theorem 144.1, collision case].

**Proof sketch.** The equal-hash witness rules out an empty log. The one-query invariant
then identifies its query with the final handler state. Freshness makes that query distinct
from the forged message. The finalization reader and fixed-width concatenation reader show
that the CRH game decodes precisely these two messages. Full domain membership supplies
the remaining two clauses of the collision predicate. -/
theorem collisionHandler_collision (H : CRH) (S : SignatureScheme)
    (hdom : ∀ n i x, H.inDom n i x = true) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) (s : Fin (H.domLen.eval n) → Bool)
    (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)))
    (hinv : L = [] ∨ ∃ (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool),
      L = [⟨j, m, hashedReply H S n sk i rs m⟩] ∧ s = m)
    (hfresh : ∀ e ∈ L, e.2.1 ≠ (splitBits a).1)
    (hsame : ∃ e ∈ L, H.hash n i e.2.1 = H.hash n i (splitBits a).1) :
    let xx := splitBits (padFin (H.domLen.eval n + H.domLen.eval n)
      ((collisionHandler H S).result n i ω s a))
    H.inDom n i xx.1 = true ∧ H.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
      H.hash n i xx.1 = H.hash n i xx.2 := by
  rcases hinv with hnil | ⟨j, m, hL, hs⟩
  · obtain ⟨e, he, _⟩ := hsame
    rw [hnil] at he
    exact False.elim (List.not_mem_nil he)
  · subst L
    subst s
    obtain ⟨e, he, hhash⟩ := hsame
    have heq := List.mem_singleton.mp he
    subst e
    have hne : m ≠ (splitBits a).1 := hfresh _ (List.mem_singleton_self _)
    have hp : (List.ofFn a).take (H.domLen.eval n) = List.ofFn (splitBits a).1 := by
      simpa only [splitBits_fst] using (EffFill.ofFn_take_drop_add a).1
    have hdecode : splitBits (padFin (H.domLen.eval n + H.domLen.eval n)
        ((collisionHandler H S).result n i ω m a)) = (m, (splitBits a).1) := by
      rw [collisionHandler_result, hp, splitBits_pad_concat]
    dsimp only
    rw [hdecode]
    exact ⟨hdom n i m, hdom n i _, hne, hhash⟩

/-- T1 realizes the collision handler as a machine: on matching seed/adversary coins,
its output equals `collisionHandler.result` after the deterministic simulation. This is
the machine-construction part of [PS10, Theorem 144.1], before relating the collision event. -/
theorem exists_collisionMachine (H : CRH) (S : SignatureScheme) (A : NUPPT) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ :
      (Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (i : List Bool) (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
        (r : A.Coins n),
        ∃ (a : Fin ((PolyExpr.add H.domLen S.sigLen).eval n) → Bool)
          (s : Fin ((collisionHandler H S).stateLen.eval n) → Bool),
          simulate ((collisionHandler H S).impl n i ω)
              (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n)
                (fun _ : Fin 1 => S.sigLen.eval n) ((PolyExpr.add H.domLen S.sigLen).eval n))
                n ((.const 1 : PolyExpr).eval n) ((collisionHandler H S).advInput n i ω) r)
              ((collisionHandler H S).init n) = .pure (a, s) ∧
            B.runAt n i (φ (ω, r)) = (collisionHandler H S).result n i ω s a :=
  exists_handlerMachine A (.const 1) (fun _ => H.domLen) (fun _ => S.sigLen)
    (.add H.domLen S.sigLen) (collisionHandler H S)

/-- T1 supplies a collision machine whose output is the finalization of the common
fixed-tape transcript. Its coins correspond bijectively to the handler seed and adversary
tape; concatenated generator/signing tapes give the same adversary output and one-query
invariant as `collisionHandler_transcript` [PS10, Theorem 144.1].

**Proof sketch.** Apply the T1 machine contract and the common-transcript coupling to the
same seed and adversary tape. Both describe the same deterministic handler simulation as
a pure computation. Injectivity of the pure constructor identifies their final outputs
and states, so the T1 run equation becomes the claimed common-transcript run equation. -/
theorem exists_collisionMachine_transcript (H : CRH) (S : SignatureScheme) (A : NUPPT) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ :
      (Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (i : List Bool) (rg : S.gen.Coins n) (rs : S.sign.Coins n)
        (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool) (rA : A.Coins n),
        List.ofFn ω = List.ofFn rg ++ List.ofFn rs →
        ∃ (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
          (s : Fin (H.domLen.eval n) → Bool)
          (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
            (fun _ => S.sigLen.eval n))),
          transcript H S A n (pairFstD (S.gen.runAt n [] rg))
            (pairSndD (S.gen.runAt n [] rg)) i rs rA = .pure (a, ((), L)) ∧
          (L = [] ∨ ∃ (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool),
            L = [⟨j, m, hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m⟩] ∧ s = m) ∧
          B.runAt n i (φ (ω, rA)) = (collisionHandler H S).result n i ω s a := by
  obtain ⟨B, hB⟩ := exists_collisionMachine H S A
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  refine ⟨φ, fun i rg rs ω rA hω => ?_⟩
  simp only [PolyExpr.eval_add, PolyExpr.eval_const] at hφ
  obtain ⟨a₀, s₀, hsim, hrun⟩ := hφ i ω rA
  obtain ⟨a, s, L, hsame, ht, hinv⟩ :=
    collisionHandler_transcript H S A n i rg rs rA ω hω
  have heq : (a₀, s₀) = (a, s) := OracleComp.pure.inj (hsim.symm.trans hsame)
  obtain ⟨ha, hs⟩ := Prod.mk.inj heq
  refine ⟨a, s, L, ht, hinv, ?_⟩
  simpa only [ha, hs] using hrun

end TCSlib.Cryptography.Authentication.HashSignFill
