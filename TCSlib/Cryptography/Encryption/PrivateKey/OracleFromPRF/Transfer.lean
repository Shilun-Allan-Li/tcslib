/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From the IND experiment to the experiment with a pad function

Generic transfer lemmas for step 1 of [PS10, Theorem 168.2]: a fixed-length private-key scheme
whose encryption with a key is `⟨r, m ⊕ f(r)⟩` with a uniform nonce `r`, and whose decryption is
`⟨1, v ⊕ f(x)⟩` on well-formed `⟨x, v⟩` and `⊥` otherwise, has, call by call, the oracles
`PRFGame.fImpl` with the pad function `f` under CPA and CCA1 (`expect_indImpl_fImpl`). The game's
codec is a bit codec (`indCodec_eq_bitCodec`), and the experiment with `f` is transported along
equal lengths (`expect_fImpl_transport`).

## Main results

* `PRFGame.expect_indImpl_fImpl`: one call of `IND_b` has the law of `fImpl`.
* `PRFGame.indCodec_eq_bitCodec`, `PRFGame.expect_fImpl_transport`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 99.1 and Theorem 168.2 (book pp. 99, 168).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

/-- **One call of `IND_b` with the key `key` has the law of `fImpl` with the pad function `fk`**
(CPA or CCA1), for every function `g` of the answer and the new state, for a scheme `S` whose
encryption with `key` is `ctOf` with the nonce `ν re` of a bijection `ν` (`henc`), whose
decryption is `⟨1, v ⊕ fk(x)⟩` on well-formed `⟨x, v⟩` and `⊥` otherwise (`hdec`), with
`(3n + 2)`-bit ciphertexts:
`𝔼[g] (S.indImpl (atkOf atkBit) b n key i x s) = 𝔼[g] (fImpl … fk i x s)`.

**Proof sketch.** By the oracle (the `_onSpec` readers). Encryption and the first challenge
sample the coins of `Enc`, which are the nonce (`expect_sample_equiv ν`), and encrypt as `ctOf`;
the selected half is `msgOf` (`ofFn_splitHalf_fst`, `_snd`). Decryption is open only before the
challenge (CCA1) or never (CPA), so the refusal of the challenge is vacuous; its coins are unused
(`expect_const`). A repeated challenge returns the record. -/
theorem expect_indImpl_fImpl (S : FixedLengthScheme) (atkBit b : Bool) (n : ℕ)
    (key : List Bool) (fk : (Fin n → Bool) → (Fin n → Bool)) (hct : S.ctLen.eval n = 3 * n + 2)
    (ν : S.enc.Coins n ≃ (Fin n → Bool))
    (henc : ∀ (m : Fin n → Bool) (re : S.enc.Coins n),
      List.ofFn (S.encryptAt n key m re) = ctOf (ν re) (List.ofFn m) (fk (ν re)))
    (hdec : ∀ (w : List Bool) (rd : S.dec.Coins n),
      List.ofFn (FixedLengthScheme.decAnswer (decodeFin n
          (S.dec.runAt n (pairEncode key w) rd))) =
        if decWF n w then
          true :: List.zipWith xor (pairSndD w) (List.ofFn (fk (padFin n (pairFstD w))))
        else List.replicate (n + 1) false)
    (i : Fin 3) (x : (S.indSpec n).dom i) (s : Option (Fin (S.ctLen.eval n) → Bool))
    (g : (S.indSpec n).rng i × Option (Fin (S.ctLen.eval n) → Bool) → ℝ) :
    expect (S.indImpl (atkOf atkBit) b n key i x s) g =
      expect (fImpl (S.inLens n) (S.outLens n) (S.ctLen.eval n) n (atkOf atkBit) b (fk) i x s)
        g := by
  have hlenCt : ∀ (r : Fin n → Bool) {m : List Bool}, m.length = n → ∀ y : Fin n → Bool,
      (ctOf r m y).length = S.ctLen.eval n := fun r m hm y => by rw [length_ctOf r hm, hct]
  match i, x with
  | 0, m =>
    rw [S.indImpl_enc_onSpec, fImpl_enc, expect_bind, expect_bind, ← expect_sample_equiv ν]
    refine congrArg _ (funext fun re => ?_)
    rw [expect_pure, expect_pure]
    have hm : List.ofFn (cast (S.indSpec_encDom n) m) = List.ofFn m :=
      ofFn_cast (S.inLens_zero n) _ m
    have hm' : cast (S.indSpec_encDom n) m = padFin n (List.ofFn m) :=
      List.ofFn_injective (by rw [hm, ofFn_padFin_of_length (by
        rw [List.length_ofFn, S.inLens_zero])])
    congr 2
    refine List.ofFn_injective ?_
    rw [ofFn_cast (S.outLens_zero n).symm _ _, hm', henc,
      ofFn_padFin_of_length (by rw [List.length_ofFn, S.inLens_zero]),
      ofFn_padFin_of_length (by
        rw [hlenCt _ (by rw [List.length_ofFn, S.inLens_zero]), S.outLens_zero])]
  | 1, c =>
    rw [S.indImpl_dec_onSpec, fImpl_dec, decOpen_atkOf]
    have hc : List.ofFn (cast (S.indSpec_decDom n) c) = List.ofFn c :=
      ofFn_cast (S.inLens_one n) _ c
    by_cases hop : (atkBit && !s.isSome) = true
    · have hs : s = none := by
        cases s with
        | none => rfl
        | some _ => simp at hop
      subst hs
      rw [if_pos (by simpa using hop), expect_bind]
      refine (congrArg _ (funext fun rd => ?_)).trans (expect_const _ _)
      rw [expect_pure, expect_pure]
      congr 2
      refine List.ofFn_injective ?_
      rw [ofFn_cast (S.outLens_one n).symm _ _, hc, hdec, decAns_eq, hop, Bool.true_and]
      by_cases hw : decWF n (List.ofFn c) = true
      · rw [if_pos hw, if_pos hw]
        rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw
        rw [ofFn_padFin_of_length (by
          rw [List.length_cons, List.length_zipWith, List.length_ofFn, hw.2, Nat.min_self,
            S.outLens_one])]
      · rw [if_neg hw, if_neg hw, padFin_nil, ofFn_zeroBits, S.outLens_one]
    · rw [Bool.not_eq_true] at hop
      rw [if_neg (by rw [hop, Bool.false_and]; exact Bool.false_ne_true), decAns_eq, hop,
        Bool.false_and, if_neg Bool.false_ne_true, expect_pure, expect_pure, padFin_nil]
  | 2, mm =>
    have hmm : List.ofFn (cast (S.indSpec_challengeDom n) mm) = List.ofFn mm :=
      ofFn_cast (S.inLens_two n) _ mm
    have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
      have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, S.inLens_two]
      rw [AdaptiveCPA.msgOf_eq]
      cases b <;> simp [this]
    have hsel : (if b then (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) mm)).2 else (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) mm)).1) =
        padFin n (AdaptiveCPA.msgOf n b (List.ofFn mm)) := by
      refine List.ofFn_injective ?_
      rw [ofFn_padFin_of_length hmsg, AdaptiveCPA.msgOf_eq, ← hmm]
      cases b
      · exact FixedLengthScheme.ofFn_splitHalf_fst _
      · exact FixedLengthScheme.ofFn_splitHalf_snd _
    cases s with
    | some c =>
      rw [S.indImpl_challenge_repeat_onSpec, fImpl_challenge_some, expect_pure, expect_pure]
      congr 2
      refine List.ofFn_injective ?_
      rw [ofFn_cast (S.outLens_two n).symm _ _,
        ofFn_padFin_of_length (by rw [List.length_ofFn, S.outLens_two])]
    | none =>
      rw [S.indImpl_challenge_none_onSpec, fImpl_challenge_none, expect_bind, expect_bind,
        ← expect_sample_equiv ν]
      refine congrArg _ (funext fun re => ?_)
      simp only [expect_pure]
      have henc' : List.ofFn (S.encryptAt n key (if b then (FixedLengthScheme.splitHalf
          (cast (S.indSpec_challengeDom n) mm)).2 else (FixedLengthScheme.splitHalf
          (cast (S.indSpec_challengeDom n) mm)).1) re) =
          ctOf (ν re) (AdaptiveCPA.msgOf n b (List.ofFn mm)) (fk (ν re)) := by
        rw [hsel, henc, ofFn_padFin_of_length hmsg]
      congr 2
      · refine List.ofFn_injective ?_
        rw [ofFn_cast (S.outLens_two n).symm _ _, henc',
          ofFn_padFin_of_length (by rw [hlenCt _ hmsg, S.outLens_two])]
      · congr 1
        refine List.ofFn_injective ?_
        rw [henc', ofFn_padFin_of_length (hlenCt _ hmsg _)]


/-- **The game's codec is the bit codec of its lengths:**
`S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1` (the three codec readers and structure
eta). -/
theorem indCodec_eq_bitCodec (S : FixedLengthScheme) (n : ℕ) :
    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := by
  have hd : (S.indCodec n).decodeMove = (bitCodec (S.inLens n) (S.outLens n) 1).decodeMove :=
    funext fun w => (S.indCodec_decodeMove n w).trans (bitCodec_decodeMove _ _ _ w).symm
  have he : (S.indCodec n).encodeEntry = (bitCodec (S.inLens n) (S.outLens n) 1).encodeEntry :=
    funext fun e => (S.indCodec_encodeEntry n e).trans (bitCodec_encodeEntry _ _ _ e).symm
  have ht : (S.indCodec n).timeout = (bitCodec (S.inLens n) (S.outLens n) 1).timeout :=
    (S.indCodec_timeout n).trans (bitCodec_timeout _ _ _).symm
  calc S.indCodec n = ⟨(S.indCodec n).decodeMove, (S.indCodec n).encodeEntry,
        (S.indCodec n).timeout⟩ := rfl
    _ = ⟨(bitCodec (S.inLens n) (S.outLens n) 1).decodeMove,
        (bitCodec (S.inLens n) (S.outLens n) 1).encodeEntry,
        (bitCodec (S.inLens n) (S.outLens n) 1).timeout⟩ := by rw [hd, he, ht]
    _ = bitCodec (S.inLens n) (S.outLens n) 1 := rfl


/-- **The game with pad function `f` along equal lengths:** for `ins = ins'`, `outs = outs'` and
`d = d'`, the expected first output bit of `A`'s run against `fImpl` agrees.

**Proof sketch.** Substitute the equalities. -/
theorem expect_fImpl_transport {ins ins' outs outs' : Fin 3 → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d') (n : ℕ) (atk : Attack) (b : Bool)
    (f : (Fin n → Bool) → (Fin n → Bool)) (A : NUPPT) (Q : ℕ) (r : A.Coins n) :
    expect (simulate (fImpl ins outs d n atk b f) (A.toComp (bitCodec ins outs 1) n Q r) none)
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
      expect (simulate (fImpl ins' outs' d' n atk b f) (A.toComp (bitCodec ins' outs' 1) n Q r)
        none) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  subst hi ho hd
  rfl

end TCSlib.Cryptography.Composability.PRFGame
