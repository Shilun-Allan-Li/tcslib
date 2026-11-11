/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hybrid games of the adaptive CPA lift

For a fixed-length public-key scheme `S`, an adversary `A`, a query budget `q` and a challenge cap
`κ`, the hybrid game `acHyb S A q κ n sel` runs `A` against the hybrid oracles `hybImpl κ E sel`
of `AdaptiveCPA.Hybrid`, where `E β mm r` encrypts the message `m_β` of the challenge query `mm`
under the generated public key with the coins `r`. The game is stated on the codec of T2
(`bitCodec` of the polynomial lengths `acDin`, `acDout`), on which the reduction of
`AdaptiveCPA.Handler` runs the adversary.

With the selector `j ↦ [j < i]` the first `i` fresh challenges encrypt the right message: this is
the hybrid `H_i` of the single-to-many argument [PS10, p. 103]. The constant selectors give the
adaptive left-or-right games (`adaptiveIndGame_eq_acHyb`), so `H_0` is the game with `b = false`
and `H_κ` the game with `b = true` (`acHyb_lt_zero`, `acHyb_lt_cap`).

## Main definitions

* `AdaptiveCPA.acEnc`: the encryption of the selected message.
* `AdaptiveCPA.acHyb`: the hybrid game with a selector.

## Main results

* `AdaptiveCPA.indCodec_eq_bitCodec`: the adversary codec is a `bitCodec`.
* `AdaptiveCPA.acDin_eval`, `acDout_eval`: the lengths of T2's codec are the game's.
* `AdaptiveCPA.castImpl_adaptiveIndImpl`: the adaptive CPA oracles, read on T2's codec, are the
  hybrid with the constant selector.
* `AdaptiveCPA.adaptiveIndGame_eq_acHyb`, `acHyb_congr`, `acHyb_lt_zero`, `acHyb_lt_cap`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 171.5 and the single-to-many hybrid argument (book p. 103).
-/

namespace TCSlib.Cryptography.Composability.AdaptiveCPA

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

variable (S : FixedLengthPKScheme)

/-! ### Codecs and lengths -/

/-- **The adversary codec is a bit codec:** `S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1`.

**Proof sketch.** Both are codecs with the same three fields (`indCodec_decodeMove`,
`indCodec_encodeEntry`, `indCodec_timeout` against the `bitCodec` readers). -/
theorem indCodec_eq_bitCodec (n : ℕ) :
    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := by
  have h1 := S.indCodec_decodeMove n
  have h2 := S.indCodec_encodeEntry n
  have h3 := S.indCodec_timeout n
  generalize S.indCodec n = c at h1 h2 h3
  cases c with
  | mk d e t =>
    have hd : d = (bitCodec (S.inLens n) (S.outLens n) 1).decodeMove :=
      funext fun w => (h1 w).trans (bitCodec_decodeMove _ _ _ w).symm
    have he : e = (bitCodec (S.inLens n) (S.outLens n) 1).encodeEntry :=
      funext fun en => (h2 en).trans (bitCodec_encodeEntry _ _ _ en).symm
    have ht : t = (bitCodec (S.inLens n) (S.outLens n) 1).timeout :=
      h3.trans (bitCodec_timeout _ _ _).symm
    rw [hd, he, ht]

/-- The query lengths of T2's codec are the game's: `(acDin S · ).eval n = S.inLens n`. -/
theorem acDin_eval (n : ℕ) : (fun i => (acDin S i).eval n) = S.inLens n := by
  funext i
  match i with
  | 0 => rw [acDin_zero, S.inLens_zero]
  | 1 => rw [acDin_one, PolyExpr.eval_add, S.inLens_one]

/-- The answer lengths of T2's codec are the game's: `(acDout S · ).eval n = S.outLens n`. -/
theorem acDout_eval (n : ℕ) : (fun i => (acDout S i).eval n) = S.outLens n := by
  funext i
  match i with
  | 0 => rw [acDout_zero, PolyExpr.eval_add, PolyExpr.eval_const, S.outLens_zero]
  | 1 => rw [acDout_one, S.outLens_one]

/-! ### Strings of the oracles -/

/-- Reading a bit vector across an equality of widths keeps its string. -/
theorem ofFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
  subst hab
  rfl

/-- The first half of a `2m`-bit query is its first `m` bits:
`⟦(splitHalf y).1⟧ = ⟦y⟧.take m`. -/
theorem ofFn_splitHalf_fst {m : ℕ} (y : Fin (m + m) → Bool) :
    List.ofFn (FixedLengthScheme.splitHalf y).1 = (List.ofFn y).take m := by
  rw [FixedLengthScheme.splitHalf_fst]
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take]; omega)
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_take, List.getElem_ofFn]
  rfl

/-- The second half of a `2m`-bit query is its last `m` bits:
`⟦(splitHalf y).2⟧ = ⟦y⟧.drop m`. -/
theorem ofFn_splitHalf_snd {m : ℕ} (y : Fin (m + m) → Bool) :
    List.ofFn (FixedLengthScheme.splitHalf y).2 = (List.ofFn y).drop m := by
  rw [FixedLengthScheme.splitHalf_snd]
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_drop]; omega)
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_drop, List.getElem_ofFn]
  rfl

/-- The all-`false` answer, read at any width, is all-`false`. -/
theorem padFin_ofFn_zeroBits (d m : ℕ) : padFin d (List.ofFn (zeroBits m)) = zeroBits d := by
  funext i
  rw [padFin_apply, ofFn_zeroBits, zeroBits_apply]
  by_cases hi : (i : ℕ) < m
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hi), List.getElem_replicate]
  · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; omega)]

/-- The bit of a one-bit output is the head of its string. -/
theorem headD_ofFn_one (f : Fin 1 → Bool) : (List.ofFn f).headD false = f 0 := by
  rw [List.ofFn_succ, List.headD_cons]

/-! ### The hybrid games -/

/-- **The encryption of the selected message:** `E β mm r = padFin (Enc_pk(m_β); r)` for the
challenge query `mm = m₀ ‖ m₁` (`msgOf`). -/
def acEnc (n : ℕ) (pk : List Bool) (β : Bool) (mm : Fin ((acDin S 1).eval n) → Bool)
    (r : S.enc.Coins n) : Fin (S.ctLen.eval n) → Bool :=
  padFin _ (S.enc.runAt n (pairEncode pk (msgOf (S.msgLen.eval n) β (List.ofFn mm))) r)

/-- `acEnc S n pk β mm r = padFin _ (S.enc.runAt n ⟨pk, msgOf m β ⟦mm⟧⟩ r)`. -/
theorem acEnc_eq (n : ℕ) (pk : List Bool) (β : Bool) (mm : Fin ((acDin S 1).eval n) → Bool)
    (r : S.enc.Coins n) :
    acEnc S n pk β mm r =
      padFin _ (S.enc.runAt n (pairEncode pk (msgOf (S.msgLen.eval n) β (List.ofFn mm))) r) :=
  rfl

/-- **The hybrid game with selector `sel`**: sample the key pair and `A`'s coins, run `A` on `pk`
through T2's codec against `hybImpl κ (acEnc S n pk) sel` from the empty history, and output its
bit. -/
noncomputable def acHyb (A : NUPPT) (q κ n : ℕ) (sel : ℕ → Bool) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (hybImpl (outs := fun i => (acDout S i).eval n) κ
      (acEnc S n (pairFstD (S.gen.runAt n [] rg))) sel)
      (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
        ((PolyExpr.const 1).eval n)) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
    fun res => .pure ((List.ofFn res.1).headD false)

/-- The defining equation of `acHyb`. -/
theorem acHyb_eq (A : NUPPT) (q κ n : ℕ) (sel : ℕ → Bool) :
    acHyb S A q κ n sel =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (hybImpl (outs := fun i => (acDout S i).eval n) κ
          (acEnc S n (pairFstD (S.gen.runAt n [] rg))) sel)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((PolyExpr.const 1).eval n)) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
        fun res => .pure ((List.ofFn res.1).headD false) :=
  rfl

/-- **Only the selector below the cap matters** (`hybImpl_congr`). -/
theorem acHyb_congr (A : NUPPT) (q κ n : ℕ) {sel sel' : ℕ → Bool}
    (hsel : ∀ j < κ, sel j = sel' j) : acHyb S A q κ n sel = acHyb S A q κ n sel' := by
  rw [acHyb_eq, acHyb_eq]
  congr 1
  funext rg
  congr 1
  funext r
  rw [hybImpl_congr κ _ sel hsel]

/-- The message selected from a challenge query by the game's oracle is `msgOf`: for the query
`x` of T2's codec, the half `b` of `splitHalf (cast (padFin ⟦x⟧))` has the string
`msgOf m b ⟦x⟧`. -/
theorem ofFn_select (n : ℕ) (x : Fin ((acDin S 1).eval n) → Bool) (b : Bool) :
    List.ofFn (if b then (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) (padFin (S.inLens n 1) (List.ofFn x)))).2
      else (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) (padFin (S.inLens n 1) (List.ofFn x)))).1) =
      msgOf (S.msgLen.eval n) b (List.ofFn x) := by
  have hx : List.ofFn (cast (S.indSpec_challengeDom n) (padFin (S.inLens n 1) (List.ofFn x))) =
      List.ofFn x := by
    rw [ofFn_cast (S.inLens_one n), GGMRed.ofFn_padFin_of_length (by
      rw [List.length_ofFn, acDin_one, PolyExpr.eval_add, S.inLens_one])]
  cases b
  · rw [if_neg Bool.false_ne_true, ofFn_splitHalf_fst, hx, msgOf_eq, if_neg Bool.false_ne_true]
  · rw [if_pos rfl, ofFn_splitHalf_snd, hx, msgOf_eq, if_pos rfl]

/-- **The adaptive CPA oracles on T2's codec are a hybrid:** read along the lengths of T2's codec,
`S.adaptiveIndImpl .cpa b n pk sk κ` is `hybImpl κ (acEnc S n pk) (fun _ => b)`.

**Proof sketch.** Oracle by oracle, through the published equations of `AdaptiveSecurity`.
Decryption answers `⊥` whether or not the query was issued (`adaptiveIndImpl_dec_issued`,
`_dec_other`, `indImpl_dec_onSpec`, `decOpen_cpa`). A fresh challenge below the cap encrypts
`m_b` with fresh coins (`adaptiveIndImpl_challenge_encrypt`; the halves of the query are
`msgOf`). At the cap the latest ciphertext is repeated (`_challenge_full`,
`indImpl_challenge_repeat_onSpec`), and an empty history has cap `0` (`_challenge_zero`). Every
width cast keeps the strings (`ofFn_cast`). -/
theorem castImpl_adaptiveIndImpl (b : Bool) (n : ℕ) (pk sk : List Bool) (κ : ℕ) :
    castImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
        (S.adaptiveIndImpl .cpa b n pk sk κ) =
      hybImpl κ (acEnc S n pk) (fun _ => b) := by
  funext i x h
  match i, x with
  | 0, x =>
    rw [castImpl_eq, hybImpl_zero]
    have hdec : S.adaptiveIndImpl .cpa b n pk sk κ 0 (padFin (S.inLens n 0) (List.ofFn x)) h =
        .pure (zeroBits _, h) := by
      by_cases hc : cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x)) ∈ h
      · exact S.adaptiveIndImpl_dec_issued .cpa b n pk sk κ _ h hc
      · rw [S.adaptiveIndImpl_dec_other .cpa b n pk sk κ _ h hc, S.indImpl_dec_onSpec,
          FixedLengthScheme.decOpen_cpa, Bool.false_and, if_neg Bool.false_ne_true,
          OracleComp.pure_bind]
    rw [hdec, OracleComp.pure_bind, padFin_ofFn_zeroBits]
  | 1, x =>
    by_cases hh : h.length < κ
    · rw [castImpl_eq, S.adaptiveIndImpl_challenge_encrypt .cpa b n pk sk κ _ h hh,
        hybImpl_fresh (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
          κ _ _ x h hh, OracleComp.bind_assoc]
      congr 1
      funext r
      dsimp only
      rw [OracleComp.pure_bind, acEnc_eq, ofFn_select, ofFn_cast (S.outLens_one n).symm]
    · cases h with
      | nil =>
        have hκ : κ = 0 := by
          rw [List.length_nil] at hh
          omega
        subst hκ
        rw [castImpl_eq, S.adaptiveIndImpl_challenge_zero, OracleComp.pure_bind,
          hybImpl_full (ins := fun i => (acDin S i).eval n)
          (outs := fun i => (acDout S i).eval n) 0 _ _ x [] le_rfl, List.headD_nil,
          padFin_ofFn_zeroBits,
          padFin_ofFn_zeroBits]
      | cons c t =>
        rw [castImpl_eq, S.adaptiveIndImpl_challenge_full .cpa b n pk sk κ _ (c :: t)
            (Nat.le_of_not_lt hh) c rfl, S.indImpl_challenge_repeat_onSpec, OracleComp.pure_bind,
          OracleComp.pure_bind, hybImpl_full (ins := fun i => (acDin S i).eval n)
          (outs := fun i => (acDout S i).eval n) κ _ _ x (c :: t) (Nat.le_of_not_lt hh),
          List.headD_cons, ofFn_cast (S.outLens_one n).symm]

/-- **The adaptive game is the hybrid game with a constant selector:**
`S.adaptiveIndGame .cpa A q κ b n = acHyb S A q κ n (fun _ => b)`.

**Proof sketch.** Fix the key-generation and adversary coins. The adversary codec is a bit codec
(`indCodec_eq_bitCodec`), its one-bit output is the head of its string (`headD_ofFn_one`), and
the run transports to T2's codec, whose lengths are equal (`simulate_castImpl_toCompOn`), where the
oracles are the hybrid (`castImpl_adaptiveIndImpl`). -/
theorem adaptiveIndGame_eq_acHyb (A : NUPPT) (q κ : ℕ) (b : Bool) (n : ℕ) :
    S.adaptiveIndGame .cpa A q κ b n = acHyb S A q κ n (fun _ => b) := by
  rw [S.adaptiveIndGame_eq, acHyb_eq]
  congr 1
  funext rg
  congr 1
  funext r
  rw [← castImpl_adaptiveIndImpl S b n (pairFstD (S.gen.runAt n [] rg))
    (pairSndD (S.gen.runAt n [] rg)) κ, indCodec_eq_bitCodec]
  have key := simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n)
    (PolyExpr.eval_const 1 n)
    (S.adaptiveIndImpl .cpa b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))
      κ) A n q (pairFstD (S.gen.runAt n [] rg)) r []
  calc _ = ((simulate (S.adaptiveIndImpl .cpa b n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) κ)
          (A.toCompOn (bitCodec (S.inLens n) (S.outLens n) 1) n q
            (pairFstD (S.gen.runAt n [] rg)) r) []).bind
          (fun p => .pure (List.ofFn p.1, p.2))).bind
          (fun p => .pure (p.1.headD false)) := by
        rw [OracleComp.bind_assoc]
        refine congrArg _ (funext fun p => ?_)
        rw [OracleComp.pure_bind, headD_ofFn_one]
    _ = _ := by
        rw [← key, OracleComp.bind_assoc]
        refine congrArg _ (funext fun p => ?_)
        rw [OracleComp.pure_bind]

/-- **The first hybrid is the game with `b = false`:** with the selector `j ↦ [j < 0]` no fresh
challenge encrypts the right message. -/
theorem acHyb_lt_zero (A : NUPPT) (q κ n : ℕ) :
    acHyb S A q κ n (fun j => decide (j < 0)) = S.adaptiveIndGame .cpa A q κ false n := by
  rw [adaptiveIndGame_eq_acHyb]
  exact acHyb_congr S A q κ n fun j _ => decide_eq_false (Nat.not_lt_zero j)

/-- **The last hybrid is the game with `b = true`:** with the selector `j ↦ [j < κ]` every fresh
challenge below the cap encrypts the right message. -/
theorem acHyb_lt_cap (A : NUPPT) (q κ n : ℕ) :
    acHyb S A q κ n (fun j => decide (j < κ)) = S.adaptiveIndGame .cpa A q κ true n := by
  rw [adaptiveIndGame_eq_acHyb]
  exact acHyb_congr S A q κ n fun j hj => decide_eq_true hj

end TCSlib.Cryptography.Composability.AdaptiveCPA
