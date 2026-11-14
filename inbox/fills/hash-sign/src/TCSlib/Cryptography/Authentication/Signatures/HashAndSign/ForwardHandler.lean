/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Forwarding
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hash-and-sign forwarding handler

The one-time forger reduction samples a hash index, gives the public key and index to
its adversary, hashes each query before forwarding it, and hashes the final message.

## Main definitions

* `HashSignForward.indexWord`: the hash index obtained from the handler's seed.
* `HashSignForward.hashWord`: the hash read at the original signature message length.
* `HashSignForward.handler`: the interactive handler of [PS10, Theorem 144.1].

## Main results

The string functions are polynomial-time, and the handler's published field equations
expose its seed, budgets, adversary input, round and finalization.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 144.1, book pp. 144–145.
-/

namespace TCSlib.Cryptography.Authentication.HashSignForward

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open InteractiveHandler

/-- The index generator on parameter word `u` and seed `ω`, with empty input and advice. -/
def indexWord (H : CRH) (u ω : List Bool) : List Bool :=
  H.gen.output (NUPPT.layout u [] [] ω)

/-- The index word is `H.gen.output (NUPPT.layout u [] [] ω)`. -/
theorem indexWord_eq (H : CRH) (u ω : List Bool) :
    indexWord H u ω = H.gen.output (NUPPT.layout u [] [] ω) := rfl

/-- The hash of `m` at index `i`, padded to the original scheme's message length. -/
def hashWord (H : CRH) (S : SignatureScheme) (u i m : List Bool) : List Bool :=
  padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m)))

/-- The hash word is the evaluator output padded to `S.msgLen(|u|)` bits. -/
theorem hashWord_eq (H : CRH) (S : SignatureScheme) (u i m : List Bool) :
    hashWord H S u i m =
      padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m))) := rfl

/-- The reduction gives its adversary the public key paired with its sampled index. -/
def advWord (H : CRH) (w : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD w))
    (indexWord H (pairFstD w) (pairSndD (pairSndD w)))

/-- The adversary input pairs the reduction input with the index obtained from its seed. -/
theorem advWord_eq (H : CRH) (w : List Bool) :
    advWord H w = pairEncode (pairFstD (pairSndD w))
      (indexWord H (pairFstD w) (pairSndD (pairSndD w))) := rfl

/-- The first round asks the original signing oracle the hashed message; the second
round returns the outer signature and preserves the state. -/
def roundWord (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
  if decide (rL w = []) then
    pairEncode [false] (pairEncode []
      (hashWord H S (rU w) (indexWord H (rU w) (rW w)) (rX w)))
  else pairEncode [true] (rAns w ++ rS w)

/-- The round asks the hashed query when its outer log is empty, and otherwise returns
the first outer answer together with its unchanged state. -/
theorem roundWord_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
    roundWord H S w =
      if decide (rL w = []) then
        pairEncode [false] (pairEncode []
          (hashWord H S (rU w) (indexWord H (rU w) (rW w)) (rX w)))
      else pairEncode [true] (rAns w ++ rS w) := rfl

/-- The finalization hashes the message prefix of the adversary output and retains
its signature suffix, making no further oracle query. -/
def finalWord (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
  pairEncode [true]
    (hashWord H S (rU w) (indexWord H (rU w) (rW w))
      ((finA w).take (H.domLen.eval (rU w).length)) ++
      (finA w).drop (H.domLen.eval (rU w).length))

/-- The final output is the hashed message prefix concatenated with the signature suffix. -/
theorem finalWord_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
    finalWord H S w = pairEncode [true]
      (hashWord H S (rU w) (indexWord H (rU w) (rW w))
        ((finA w).take (H.domLen.eval (rU w).length)) ++
        (finA w).drop (H.domLen.eval (rU w).length)) := rfl

/-- Running the index generator on polynomial-time parameter and seed words is
polynomial-time. -/
theorem polyTimeComputable_indexWord (H : CRH) {u ω : List Bool → List Bool}
    (hu : PolyTimeComputable u) (hω : PolyTimeComputable ω) :
    PolyTimeComputable fun w => indexWord H (u w) (ω w) := by
  simpa only [indexWord, Function.comp_apply] using
    H.gen.polyTimeComputable_output.comp
      (NUPPT.polyTimeComputable_layout hu (polyTimeComputable_const [])
        (polyTimeComputable_const []) hω)

/-- Hashing polynomial-time parameter, index and message words and padding the result
to the original signature message length is polynomial-time. -/
theorem polyTimeComputable_hashWord (H : CRH) (S : SignatureScheme)
    {u i m : List Bool → List Bool} (hu : PolyTimeComputable u)
    (hi : PolyTimeComputable i) (hm : PolyTimeComputable m) :
    PolyTimeComputable fun w => hashWord H S (u w) (i w) (m w) := by
  have h := (polyTimeComputable_padStr S.msgLen).comp
    (hu.pairEncode (H.eval_poly.comp (hu.pairEncode (hi.pairEncode hm))))
  refine (congrArg PolyTimeComputable
    (?_ : (fun w => hashWord H S (u w) (i w) (m w)) = _)).mpr h
  funext w
  simp only [hashWord_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- Pairing the supplied public key with the index generated from the seed is
polynomial-time. -/
theorem polyTimeComputable_advWord (H : CRH) : PolyTimeComputable (advWord H) := by
  exact (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).pairEncode
    (polyTimeComputable_indexWord H polyTimeComputable_pairFstD
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- One hashing-and-forwarding round is polynomial-time: it tests whether the outer
log is empty, then either emits the hash query or returns the recorded answer. -/
theorem polyTimeComputable_roundWord (H : CRH) (S : SignatureScheme) :
    PolyTimeComputable (roundWord H S) := by
  exact polyTimeComputable_ite
    (polyTimeComputable_isNil.comp polyTimeComputable_rL)
    ((polyTimeComputable_const [false]).pairEncode
      ((polyTimeComputable_const []).pairEncode
        (polyTimeComputable_hashWord H S polyTimeComputable_rU
          (polyTimeComputable_indexWord H polyTimeComputable_rU polyTimeComputable_rW)
          polyTimeComputable_rX)))
    ((polyTimeComputable_const [true]).pairEncode
      (polyTimeComputable_rAns.append polyTimeComputable_rS))

/-- Finalization is polynomial-time: split at the polynomial domain width, hash the
message prefix and concatenate the original signature suffix.

**Proof sketch.** The published polynomial take and drop operations apply to the parameter
and output fields. The parameter, seed and output readers and the index and hash operations
are polynomial-time, so composition and concatenation give the result. -/
theorem polyTimeComputable_finalWord (H : CRH) (S : SignatureScheme) :
    PolyTimeComputable (finalWord H S) := by
  have hm := (polyTimeComputable_pairTakePoly H.domLen).comp
    (polyTimeComputable_rU.pairEncode polyTimeComputable_finA)
  have hs := (polyTimeComputable_pairDropPoly H.domLen).comp
    (polyTimeComputable_rU.pairEncode polyTimeComputable_finA)
  have h := (polyTimeComputable_const [true]).pairEncode
    ((polyTimeComputable_hashWord H S polyTimeComputable_rU
      (polyTimeComputable_indexWord H polyTimeComputable_rU polyTimeComputable_rW) hm).append hs)
  refine (congrArg PolyTimeComputable (?_ : finalWord H S = _)).mpr h
  funext w
  simp only [finalWord_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The hash-and-sign reduction handler [PS10, Theorem 144.1]: sample one hash index,
provide `⟨pk,i⟩`, forward each query after hashing it, and hash the final message. Its state
is empty, each inner call makes one outer call and finalization makes none. -/
def handler (H : CRH) (S : SignatureScheme) :
    InteractiveHandler 1 (fun _ => H.domLen) (fun _ => S.sigLen)
      1 (fun _ => S.msgLen) (fun _ => S.sigLen) where
  stateLen := .const 0
  seedLen := H.gen.coins
  perCall := .const 1
  init _ := zeroBits _
  run := roundWord H S
  poly := polyTimeComputable_roundWord H S
  advIn := advWord H
  advIn_poly := polyTimeComputable_advWord H
  outLen := .add S.msgLen S.sigLen
  finCall := .const 0
  finRun := finalWord H S
  finRun_poly := polyTimeComputable_finalWord H S

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init run advIn outLen
  finCall finRun] handler

/-- At a unary parameter, the generated index word is the hash generator's literal run
with the supplied list of coins. -/
theorem indexWord_unary (H : CRH) (n : ℕ) (ω : List Bool) :
    indexWord H (List.replicate n true) ω = H.gen.runAtL n [] ω := by
  rw [indexWord_eq, H.gen_uniform.runAtL_eq, NUPPT.layout_eq, NUPPT.advInput_eq]

/-- At unary parameter `1^n`, the hash word is the list of the padded evaluator at
the original signature message length. -/
theorem hashWord_unary (H : CRH) (S : SignatureScheme) (n : ℕ) (i m : List Bool) :
    hashWord H S (List.replicate n true) i m =
      List.ofFn (padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i m)))) := by
  rw [hashWord_eq, ← ofFn_padFin_eq_padStr, List.length_replicate, atParam_eq]

/-- The handler gives the adversary `⟨pk,i⟩`, where `i` is the hash generator's run
on its seed. -/
theorem handler_advInput (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
    (ω : Fin ((handler H S).seedLen.eval n) → Bool) :
    (handler H S).advInput n pk ω =
      pairEncode pk (H.gen.runAtL n [] (List.ofFn ω)) := by
  rw [InteractiveHandler.advInput_eq, handler_advIn, advWord_eq, seedIn_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, indexWord_unary]

/-- Each call asks the original signing oracle for the hash of its inner message and
returns the outer signature unchanged, preserving the handler state.

**Proof sketch.** The first round has an empty outer log and emits precisely the padded
hash query. The second round reads the first outer answer and returns it with the state.
The published one-query call rule therefore identifies the entire call computation. -/
theorem handler_impl (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
    (ω : Fin ((handler H S).seedLen.eval n) → Bool) (i : Fin 1)
    (x : Fin (H.domLen.eval n) → Bool)
    (s : Fin ((handler H S).stateLen.eval n) → Bool) :
    (handler H S).impl n pk ω i x s =
      .query 0
        (padFin (S.msgLen.eval n) (H.eval
          (atParam n (pairEncode (H.gen.runAtL n [] (List.ofFn ω)) (List.ofFn x)))))
        fun y => .pure (y, s) := by
  refine InteractiveHandler.impl_of_query (handler H S) n pk ω x s 0 _
    (fun y => y) (fun _ => s) ?_ ?_ ?_
  · rw [handler_perCall, PolyExpr.eval_const]
  · rw [handler_run, roundWord_eq, rL_input, rU_input, rW_input, rX_input,
      indexWord_unary, hashWord_unary, if_pos (decide_eq_true rfl)]
    rfl
  · intro y
    rw [handler_run, roundWord_eq, rL_input, rAns_input, rS_input,
      if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h))]

/-- Finalization makes no oracle query and returns the hash of the adversary's message
prefix concatenated with its signature suffix, read at the handler's output length.

**Proof sketch.** The hash word has the signature scheme's message width. The suffix of
the correctly sized adversary output has the signature width, so the concatenation has
the declared output width. The first finalization round returns this word; the published
immediate-return finalization rule identifies its computation. -/
theorem handler_finish (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
    (ω : Fin ((handler H S).seedLen.eval n) → Bool)
    (s : Fin ((handler H S).stateLen.eval n) → Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    (handler H S).finish n pk ω s a =
      .pure (padFin ((handler H S).outLen.eval n)
        (hashWord H S (List.replicate n true) (H.gen.runAtL n [] (List.ofFn ω))
          ((List.ofFn a).take (H.domLen.eval n)) ++
          (List.ofFn a).drop (H.domLen.eval n))) := by
  refine InteractiveHandler.finish_of_ret_padFin (handler H S) n pk ω s a _ ?_ ?_
  · rw [List.length_append, hashWord_unary, List.length_ofFn, List.length_drop,
      List.length_ofFn, handler_outLen, PolyExpr.eval_add]
    omega
  · rw [handler_finRun, finalWord_eq, rU_finInput, rW_finInput, finA_finInput,
      indexWord_unary, List.length_replicate]

/-- When the hash range and signature message widths agree, hashing a typed domain
message gives the list of the CRH hash, transported to the signature message width. -/
theorem hashWord_eq_hash (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (i : List Bool)
    (x : Fin (H.domLen.eval n) → Bool) :
    hashWord H S (List.replicate n true) i (List.ofFn x) =
      List.ofFn (fun j : Fin (S.msgLen.eval n) =>
        H.hash n i x (Fin.cast (hlen n).symm j)) := by
  rw [hashWord_unary]
  apply congrArg List.ofFn
  funext j
  rw [CRH.hash_eq, padFin_apply, padFin_apply, Fin.coe_cast]

/-- The hash-and-sign forwarding reduction is a one-query oracle machine
[PS10, Theorem 144.1]. For every parameter, a bijection identifies its coins with the
handler seed and the original adversary coins, and its computation is the handler's
simulation followed by finalization.

**Proof sketch.** Apply T2 to the hashing handler and the constant-one inner query
budget. One outer query per inner query and zero finalization queries give outer
budget `1 · 1 + 0 = 1`; the codec widths are the signature message and signature widths. -/
theorem exists_forwardMachine (H : CRH) (S : SignatureScheme) (A : NUPPT) :
    ∃ C : NUPPT, ∀ n : ℕ,
      ∃ φ : (Fin ((handler H S).seedLen.eval n) → Bool) × A.Coins n ≃ C.Coins n,
        ∀ (pk : List Bool) (ω : Fin ((handler H S).seedLen.eval n) → Bool)
          (r : A.Coins n),
          (simulate ((handler H S).impl n pk ω)
            (A.toCompOn
              (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
                (H.domLen.eval n + S.sigLen.eval n))
              n 1 ((handler H S).advInput n pk ω) r)
            ((handler H S).init n)).bind
              (fun res => (handler H S).finish n pk ω res.2 res.1) =
            C.toCompOn
              (bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
                (S.msgLen.eval n + S.sigLen.eval n))
              n 1 pk (φ (ω, r)) := by
  obtain ⟨C, hC⟩ := exists_interactiveHandlerMachine A (.const 1)
    (fun _ : Fin 1 => H.domLen) (fun _ => S.sigLen)
    (fun _ : Fin 1 => S.msgLen) (fun _ => S.sigLen)
    (.add H.domLen S.sigLen) (handler H S)
  simp only [PolyExpr.eval_const, PolyExpr.eval_add, handler_perCall,
    handler_finCall, handler_outLen, Nat.one_mul, Nat.add_zero] at hC
  exact ⟨C, hC⟩

/-- The handler output width is the sum of the original message and signature widths. -/
theorem handler_output_width (H : CRH) (S : SignatureScheme) (n : ℕ) :
    (handler H S).outLen.eval n = S.msgLen.eval n + S.sigLen.eval n :=
  (congrArg (fun p : PolyExpr => p.eval n) (handler_outLen H S)).trans
    (PolyExpr.eval_add S.msgLen S.sigLen n)

/-- Finalization returns the hashed message component paired by concatenation with
the adversary's signature component. The displayed cast transports the declared handler
output width to the sum of message and signature widths.

**Proof sketch.** Read finalization as a padded list, split the adversary list at the
domain width with the published take/drop lemma, and identify the concatenation as the
list of a `Fin.append` vector. Reading that list at its width recovers the vector. -/
theorem handler_finish_split (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
    (ω : Fin ((handler H S).seedLen.eval n) → Bool)
    (s : Fin ((handler H S).stateLen.eval n) → Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    (handler H S).finish n pk ω s a =
      .pure (fun j =>
        Fin.append
          (padFin (S.msgLen.eval n) (H.eval (atParam n
            (pairEncode (H.gen.runAtL n [] (List.ofFn ω))
              (List.ofFn (splitBits a).1)))))
          (splitBits a).2 (Fin.cast (handler_output_width H S n) j)) := by
  have hf : (splitBits a).1 = fun j => a (Fin.castAdd (S.sigLen.eval n) j) :=
    funext fun j => splitBits_fst a j
  have hs : (splitBits a).2 = fun j => a (Fin.natAdd (H.domLen.eval n) j) :=
    funext fun j => splitBits_snd a j
  rw [hf, hs]
  rw [handler_finish, (EffFill.ofFn_take_drop_add a).1,
    (EffFill.ofFn_take_drop_add a).2, hashWord_unary, ← List.ofFn_fin_append]
  congr 1
  funext j
  rw [padFin_apply, ← Fin.coe_cast (handler_output_width H S n) j,
    ← padFin_apply, padFin_ofFn]

end TCSlib.Cryptography.Authentication.HashSignForward
