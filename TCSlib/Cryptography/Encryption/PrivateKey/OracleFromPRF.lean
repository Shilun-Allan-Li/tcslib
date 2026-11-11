/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The §3.9 scheme under chosen-plaintext and chosen-ciphertext attacks (statement phase)

[PS10, Theorem 168.2]: the scheme of Algorithm 99.1 (the ch. 2–4 layer's `prfScheme`:
`Enc_k(m) = ⟨r, m ⊕ f_k(r)⟩` for a fresh uniform `r`) is CPA- and CCA1-secure when `F` is a PRF.
[PS10, §7.1.3, Claim 169.a in the inventory]: it is not CCA2-secure, whatever `F`.

The CCA1 statement relies on `Dec` refusing malformed ciphertexts (`prfDecWF`): the evaluator `E`
agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`, and a decryption query must not reach it
elsewhere.

## Main definitions

* `Composability.prfFixedScheme`: `prfScheme`, whose ciphertexts have `3n + 2` bits.

## Main results

* `Composability.prfFixedScheme_cpa`, `Composability.prfFixedScheme_cca1` (Thm 168.2, stated;
  `sorry`s under the source's sketch).
* `Composability.prfFixedScheme_not_cca2` (Claim 169.a, proved): an explicit adversary with
  advantage `1`.
* `Composability.not_prfFixedScheme_cca2`: hence the scheme is not CCA2-secure (proved from the
  claim).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 99.1, Theorem 168.2 and §7.1.3 (book pp. 99, 168–169; the theorem calls the algorithm
  "construction 99.1").
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))

/-- **The §3.9 scheme with fixed-length ciphertexts**: `⟨r, m ⊕ f_k(r)⟩` with `r` and `m` of `n`
bits has `2n + 2 + n = 3n + 2` bits. -/
noncomputable def prfFixedScheme : FixedLengthScheme where
  toPrivateKeyScheme := prfScheme F E hE hFE
  ctLen := .add (.mul (.const 3) .var) (.const 2)
  enc_length := by
    simp only [prfScheme_gen, prfScheme_enc]
    intro n rg m r
    have hlen : ∀ {f : List Bool → List Bool} (hf : PolyTimeComputable f),
        (NUPPT.ofPolyTimeUniform hf .var).coinLen n = n :=
      fun {f} hf => (NUPPT.coinLen_eq (NUPPT.ofPolyTimeUniform hf .var) n).trans
        ((congrArg (fun p : PolyExpr => p.eval n)
          (NUPPT.coins_ofPolyTimeUniform hf .var)).trans (PolyExpr.eval_var n))
    let k : Fin n → Bool := fun j =>
      rg (Fin.cast (hlen polyTimeComputable_pairSndD).symm j)
    let x : Fin n → Bool := fun j =>
      r (Fin.cast (hlen (polyTimeComputable_prfEncFun hE)).symm j)
    have hk : List.ofFn rg = List.ofFn k :=
      List.ofFn_congr (hlen polyTimeComputable_pairSndD) rg
    have hx : List.ofFn r = List.ofFn x :=
      List.ofFn_congr (hlen (polyTimeComputable_prfEncFun hE)) r
    rw [runAt_coinKey, runAt_prfEnc hE, hk, hx, hFE, length_pairEncode]
    simp only [List.length_zipWith, List.length_ofFn, Nat.min_self, PolyExpr.eval_add,
      PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega

attribute [simps (config := { isSimp := false }) toPrivateKeyScheme ctLen] prfFixedScheme

/-- The fixed-length scheme uses the key generator of `prfScheme`. -/
theorem prfFixedScheme_gen :
    (prfFixedScheme F E hE hFE).gen = (prfScheme F E hE hFE).gen :=
  congrArg PrivateKeyScheme.gen (prfFixedScheme_toPrivateKeyScheme F E hE hFE)

/-- The fixed-length scheme uses the encryption machine of `prfScheme`. -/
theorem prfFixedScheme_enc :
    (prfFixedScheme F E hE hFE).enc = (prfScheme F E hE hFE).enc :=
  congrArg PrivateKeyScheme.enc (prfFixedScheme_toPrivateKeyScheme F E hE hFE)

/-- The fixed-length scheme uses the decryption machine of `prfScheme`. -/
theorem prfFixedScheme_dec :
    (prfFixedScheme F E hE hFE).dec = (prfScheme F E hE hFE).dec :=
  congrArg PrivateKeyScheme.dec (prfFixedScheme_toPrivateKeyScheme F E hE hFE)

/-- **Theorem 168.2 (CPA)** [PS10]: if `F` is a pseudorandom function family, the §3.9 scheme is
CPA-secure.

**Proof sketch** (the source's).
1. Replace `f_k` by a random function: by PRF security, the advantage changes by a negligible
   amount (the reduction answers `Enc` and the challenge by querying its own oracle at the fresh
   `r`). T2 (`Games.exists_interactiveHandlerMachine`) implements this forwarding handler,
   with the challenge bit in the seed and a finalization that compares the guess with that
   bit; the input-free companion and T4 (`Games.exists_toOracleAdversary_of_bitCodec`)
   supply the oracle adversary used by `OracleEnsemble.Indist`.
2. With a random function, the challenge's pad `RF(r*)` is uniform and independent of everything
   else unless `r*` collides with the `r` of some `Enc` answer. A collision has probability at most
   `q(n) / 2^n` (the collision bound `prob_mem_le`, one fresh draw against at most `q` earlier
   ones).
3. Off the collision, `m_b ⊕ RF(r*)` is uniform for both `b` (identical until bad,
   `identical_until_bad`), so the advantage is at most `q(n)/2^n` plus the PRF advantage:
   negligible. -/
theorem prfFixedScheme_cpa (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cpa := by
  sorry

/-- **Theorem 168.2 (CCA1)** [PS10]: if `F` is a pseudorandom function family, the §3.9 scheme
is CCA1-secure.

**Proof sketch** (the source's). As for CPA, with the reduction also answering decryption
queries before the challenge with its oracle (`Dec_k(⟨r, c⟩) = c ⊕ f_k(r)` on well-formed
ciphertexts, `runAt_prfDec`; `⊥` on the others, `decodeFin_runAt_prfDec_of_not_wf`). The bad event
adds the case that a pre-challenge decryption query used the challenge's `r*`, again at most
`q(n)/2^n`, because `r*` is drawn after those queries. -/
theorem prfFixedScheme_cca1 (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cca1 := by
  sorry

/-- Reverse the word, negate its first bit, and reverse back: on a nonempty word this
flips exactly its last bit. -/
private def cca2FlipLast (w : List Bool) : List Bool :=
  ([!w.reverse.headD false] ++ w.reverse.drop 1).reverse

/-- Flipping the last bit is polynomial-time by reversal, head, tail and negation. -/
private theorem cca2FlipLast_poly : PolyTimeComputable cca2FlipLast := by
  exact (BinArith.polyTimeComputable_reverse.comp
    ((polyTimeComputable_not (polyTimeComputable_headD.comp
      BinArith.polyTimeComputable_reverse)).append
        (polyTimeComputable_tail.comp BinArith.polyTimeComputable_reverse)))

/-- On a word ending in `b`, the flip replaces that bit by `!b`. -/
private theorem cca2FlipLast_snoc (w : List Bool) (b : Bool) :
    cca2FlipLast (w ++ [b]) = w ++ [!b] := by
  simp only [cca2FlipLast, List.reverse_append, List.reverse_nil, List.nil_append,
    List.singleton_append, List.headD_cons, List.drop_succ_cons, List.drop_zero,
    List.reverse_cons, List.reverse_reverse]

/-- A nonempty suffix contains the last bit, so a prefix is unchanged by the flip. -/
private theorem cca2FlipLast_append (u v : List Bool) (hv : v ≠ []) :
    cca2FlipLast (u ++ v) = u ++ cca2FlipLast v := by
  rcases List.eq_nil_or_concat' v with h | ⟨v, b, rfl⟩
  · exact (hv h).elim
  · simp only [← List.append_assoc, cca2FlipLast_snoc]

/-- Flipping a nonempty ciphertext payload preserves the nonce and pairing delimiter. -/
private theorem cca2FlipLast_pair (u v : List Bool) (hv : v ≠ []) :
    cca2FlipLast (pairEncode u v) = pairEncode u (cca2FlipLast v) := by
  rw [pairEncode_eq, pairEncode_eq, cca2FlipLast_append _ v hv]

/-- The modified word has its original length whenever that word is nonempty. -/
private theorem cca2FlipLast_length (w : List Bool) (hw : w ≠ []) :
    (cca2FlipLast w).length = w.length := by
  rcases List.eq_nil_or_concat' w with h | ⟨w, b, rfl⟩
  · exact (hw h).elim
  · simp only [cca2FlipLast_snoc, List.length_append, List.length_singleton]

/-- The flipped word differs from the original at its last bit. -/
private theorem cca2FlipLast_ne (w : List Bool) (hw : w ≠ []) :
    cca2FlipLast w ≠ w := by
  rcases List.eq_nil_or_concat' w with h | ⟨w, b, rfl⟩
  · exact (hw h).elim
  · rw [cca2FlipLast_snoc]
    intro he
    have hb := congrArg (fun v : List Bool => v.getLastD false) he
    simp only [List.getLastD_concat] at hb
    cases b <;> cases hb

/-- Negate precisely the bit whose index is one less than the vector length. -/
private def cca2FlipBits {n : ℕ} (m : Fin n → Bool) : Fin n → Bool :=
  fun i => if i.val + 1 = n then !m i else m i

/-- The list and vector versions of the last-bit flip agree at positive lengths. -/
private theorem cca2FlipLast_ofFn {n : ℕ} (hn : 0 < n) (m : Fin n → Bool) :
    cca2FlipLast (List.ofFn m) = List.ofFn (cca2FlipBits m) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [List.ofFn_succ_last, cca2FlipLast_snoc, List.ofFn_succ_last]
    congr 1
    · apply congrArg List.ofFn
      funext i
      have hi : i.val + 1 ≠ n + 1 := by omega
      change m i.castSucc = if i.val + 1 = n + 1 then !m i.castSucc else m i.castSucc
      rw [if_neg hi]
    · change [!m (Fin.last n)] =
        [if n + 1 = n + 1 then !m (Fin.last n) else m (Fin.last n)]
      rw [if_pos rfl]

/-- Flipping one bit commutes with removing an exclusive-or pad. -/
private theorem cca2FlipBits_unmask {n : ℕ} (m p : Fin n → Bool) :
    cca2FlipBits (m + p) + p = cca2FlipBits m := by
  funext i
  change xor (if i.val + 1 = n then !(xor (m i) (p i)) else xor (m i) (p i)) (p i) =
    if i.val + 1 = n then !m i else m i
  split <;> cases m i <;> cases p i <;> rfl

/-- The attack's next activation asks the challenge, asks decryption of the modified
challenge, or negates the last bit of the second answer, according to the log. -/
private def cca2Next (z : List Bool) : List Bool :=
  let h := NUPPT.inArg z
  if h = [] then
    pairEncode [false] (pairEncode [true, true]
      (List.zipWith xor (NUPPT.inParam z) (NUPPT.inParam z) ++ NUPPT.inParam z))
  else if pairSndD h = [] then
    pairEncode [false] (pairEncode [true]
      (cca2FlipLast (pairSndD (pairSndD (pairFstD h)))))
  else pairEncode [true]
    [!(pairSndD (pairSndD (pairFstD (pairSndD h)))).getLastD false]

/-- The three activations are polynomial-time: projections, emptiness tests, pairing,
exclusive-or, the last-bit flip, and a last-bit test followed by negation. -/
private theorem cca2Next_poly : PolyTimeComputable cca2Next := by
  have ha := NUPPT.polyTimeComputable_inArg
  have hp := NUPPT.polyTimeComputable_inParam
  have ht := polyTimeComputable_pairSndD.comp ha
  have hz : PolyTimeComputable (fun z =>
      List.zipWith xor (NUPPT.inParam z) (NUPPT.inParam z)) :=
    (polyTimeComputable_pairXor.comp (hp.pairEncode hp)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hans : PolyTimeComputable (fun z => pairSndD (pairSndD (pairFstD z))) :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp ha)
    ((polyTimeComputable_const [false]).pairEncode
      ((polyTimeComputable_const [true, true]).pairEncode
        (hz.append hp)))
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp ht)
      ((polyTimeComputable_const [false]).pairEncode
        ((polyTimeComputable_const [true]).pairEncode
          (cca2FlipLast_poly.comp (hans.comp ha))))
      ((polyTimeComputable_const [true]).pairEncode
        (polyTimeComputable_not (BinArith.polyTimeComputable_lastBit.comp (hans.comp ht)))))
  exact h.congr fun z => by
    simp only [cca2Next, Function.comp_apply, decide_eq_true_eq]

/-- The uniform deterministic machine implementing the three activations. -/
private noncomputable def cca2Adversary : NUPPT :=
  NUPPT.ofPolyTimeUniform cca2Next_poly (.const 0)

/-- An activation reads only its argument and the unary parameter; its coins are ignored. -/
private theorem cca2Adversary_run (n : ℕ) (h : List Bool) (r : cca2Adversary.Coins n) :
    cca2Adversary.runAt n h r =
      if h = [] then
        pairEncode [false] (pairEncode [true, true]
          (List.replicate n false ++ List.replicate n true))
      else if pairSndD h = [] then
        pairEncode [false] (pairEncode [true]
          (cca2FlipLast (pairSndD (pairSndD (pairFstD h)))))
      else pairEncode [true]
        [!(pairSndD (pairSndD (pairFstD (pairSndD h)))).getLastD false] := by
  unfold cca2Adversary
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, cca2Next]
  simp only [NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, List.zipWith_replicate,
    Nat.min_self, Bool.xor_self]

/-- A one-entry log makes the second activation query the flipped challenge answer. -/
private theorem cca2Adversary_one (n : ℕ) (i x c : List Bool)
    (r : cca2Adversary.Coins n) :
    cca2Adversary.runAt n (pairEncode (pairEncode i (pairEncode x c)) []) r =
      pairEncode [false] (pairEncode [true] (cca2FlipLast c)) := by
  rw [cca2Adversary_run]
  have hn : pairEncode (pairEncode i (pairEncode x c)) [] ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [length_pairEncode, List.length_nil] at hh
    omega
  simp only [hn, ite_false, pairFstD_pairEncode, pairSndD_pairEncode, ite_true]

/-- A two-entry log makes the final activation negate the last bit of its second answer. -/
private theorem cca2Adversary_two (n : ℕ) (i x c j y d : List Bool)
    (r : cca2Adversary.Coins n) :
    cca2Adversary.runAt n
      (pairEncode (pairEncode i (pairEncode x c))
        (pairEncode (pairEncode j (pairEncode y d)) [])) r =
      pairEncode [true] [!d.getLastD false] := by
  rw [cca2Adversary_run]
  have hn : ∀ a b : List Bool, pairEncode a b ≠ [] := by
    intro a b he
    have hh := congrArg List.length he
    simp only [length_pairEncode, List.length_nil] at hh
    omega
  simp only [hn, ite_false, pairFstD_pairEncode, pairSndD_pairEncode]

/-- For every encryption tape there is an `n`-bit nonce `x`; the ciphertext is exactly
the pair of that nonce and the message masked by `F n k x`. -/
private theorem cca2Encrypt (n : ℕ) (k m : Fin n → Bool)
    (r : (prfFixedScheme F E hE hFE).enc.Coins n) :
    ∃ x : Fin n → Bool, List.ofFn r = List.ofFn x ∧
      List.ofFn ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r) =
        pairEncode (List.ofFn x) (List.ofFn (m + F n k x)) := by
  revert r
  simp only [FixedLengthScheme.encryptAt_eq, prfFixedScheme_ctLen]
  rw [prfFixedScheme_enc, prfScheme_enc]
  intro r
  let x := NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var n r
  have hx : List.ofFn x = List.ofFn r :=
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n r
  refine ⟨x, hx.symm, ?_⟩
  rw [runAt_prfEnc hE, ← hx, hFE, zipWith_xor_ofFn_add]
  apply GGMRed.ofFn_padFin_of_length
  simp only [length_pairEncode, List.length_ofFn, PolyExpr.eval_add,
    PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- The challenge query concatenates the all-false and all-true messages. -/
private def cca2Messages (n : ℕ) : Fin (n + n) → Bool :=
  Fin.append (fun _ => false) (fun _ => true)

/-- The challenge query's word is `0^n ++ 1^n`. -/
private theorem cca2Messages_ofFn (n : ℕ) :
    List.ofFn (cca2Messages n) = List.replicate n false ++ List.replicate n true := by
  rw [cca2Messages, List.ofFn_fin_append, List.ofFn_const, List.ofFn_const]

/-- Selecting challenge half `b` selects the constant message `b`. -/
private theorem cca2Messages_choice (n : ℕ) (b : Bool) :
    (if b then (FixedLengthScheme.splitHalf (cca2Messages n)).2
      else (FixedLengthScheme.splitHalf (cca2Messages n)).1) = fun _ => b := by
  cases b with
  | false =>
    change (FixedLengthScheme.splitHalf (cca2Messages n)).1 = fun _ => false
    rw [FixedLengthScheme.splitHalf_fst]
    funext i
    exact Fin.append_left _ _ i
  | true =>
    change (FixedLengthScheme.splitHalf (cca2Messages n)).2 = fun _ => true
    rw [FixedLengthScheme.splitHalf_snd]
    funext i
    exact Fin.append_right _ _ i

/-- The modified fixed-width ciphertext reads the word with its last bit flipped. -/
private def cca2Alter {d : ℕ} (c : Fin d → Bool) : Fin d → Bool :=
  padFin d (cca2FlipLast (List.ofFn c))

/-- At positive width the modified ciphertext has exactly the flipped word. -/
private theorem cca2Alter_ofFn {d : ℕ} (hd : 0 < d) (c : Fin d → Bool) :
    List.ofFn (cca2Alter c) = cca2FlipLast (List.ofFn c) := by
  apply GGMRed.ofFn_padFin_of_length
  rw [cca2FlipLast_length]
  · exact List.length_ofFn
  · intro he
    have hh := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at hh
    omega

/-- At positive width the modified ciphertext differs from the recorded challenge. -/
private theorem cca2Alter_ne {d : ℕ} (hd : 0 < d) (c : Fin d → Bool) :
    cca2Alter c ≠ c := by
  intro he
  have hh := congrArg List.ofFn he
  rw [cca2Alter_ofFn hd] at hh
  apply cca2FlipLast_ne (List.ofFn c) ?_ hh
  intro hc
  have hl := congrArg List.length hc
  simp only [List.length_ofFn, List.length_nil] at hl
  omega

/-- The ciphertext width evaluates to `3 * n + 2`. -/
private theorem cca2CtLen (n : ℕ) :
    (prfFixedScheme F E hE hFE).ctLen.eval n = 3 * n + 2 := by
  rw [prfFixedScheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul,
    PolyExpr.eval_const, PolyExpr.eval_const, PolyExpr.eval_var]

/-- Every generated key is an `n`-bit word. -/
private theorem cca2Gen (n : ℕ) (rg : (prfFixedScheme F E hE hFE).gen.Coins n) :
    ∃ k : Fin n → Bool, (prfFixedScheme F E hE hFE).gen.runAt n [] rg = List.ofFn k := by
  revert rg
  rw [prfFixedScheme_gen, prfScheme_gen]
  intro rg
  rw [runAt_coinKey]
  exact ⟨NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n rg,
    (NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n rg).symm⟩

/-- The actual encrypted word is well formed, and its last-bit modification is a
distinct, well-formed pair with the same nonce and the flipped masked payload. -/
private theorem cca2Cipher (n : ℕ) (hn : 0 < n) (k m : Fin n → Bool)
    (r : (prfFixedScheme F E hE hFE).enc.Coins n) :
    ∃ x : Fin n → Bool,
      List.ofFn ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r) =
        pairEncode (List.ofFn x) (List.ofFn (m + F n k x)) ∧
      List.ofFn (cca2Alter ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r)) =
        pairEncode (List.ofFn x) (List.ofFn (cca2FlipBits (m + F n k x))) ∧
      cca2Alter ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r) ≠
        (prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r := by
  obtain ⟨x, -, hc⟩ := cca2Encrypt F E hE hFE n k m r
  have hd : 0 < (prfFixedScheme F E hE hFE).ctLen.eval n := by
    rw [cca2CtLen]
    omega
  have hp : List.ofFn (m + F n k x) ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at hh
    omega
  refine ⟨x, hc, ?_, cca2Alter_ne hd _⟩
  rw [cca2Alter_ofFn hd, hc, cca2FlipLast_pair _ _ hp, cca2FlipLast_ofFn hn]

/-- Decrypting a pair `⟨x, v⟩` of `n`-bit words under the key `k` unmasks it:
`Dec_k(⟨x, v⟩) = v ⊕ F n k x`, read as an `n`-bit message. -/
private theorem cca2Decrypt (n : ℕ) (k x v : Fin n → Bool)
    (rd : (prfFixedScheme F E hE hFE).dec.Coins n) :
    decodeFin n ((prfFixedScheme F E hE hFE).dec.runAt n
      (pairEncode (List.ofFn k) (pairEncode (List.ofFn x) (List.ofFn v))) rd) =
        some (v + F n k x) := by
  revert rd
  rw [prfFixedScheme_dec, prfScheme_dec]
  intro rd
  rw [runAt_prfDec hE _ n _ _ _ List.length_ofFn List.length_ofFn, hFE, zipWith_xor_ofFn_add,
    decodeFin_ofFn]

/-- Transporting a bit vector along a width equality does not change its word:
`List.ofFn (cast h f) = List.ofFn f` when `h` comes from `a = b`. -/
private theorem cca2OfFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
  subst hab
  rfl

/-- At `n > 0`, the valid answer `⟨1, b^n ⊕ e_{n-1}⟩` ends in `!b`. -/
private theorem cca2LastBit {n : ℕ} (hn : 0 < n) (b : Bool) :
    (List.ofFn (Fin.cons (α := fun _ => Bool) true (cca2FlipBits (n := n) fun _ => b))).getLastD
      false = !b := by
  rw [List.ofFn_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  rw [← cca2FlipLast_ofFn hn, List.ofFn_const]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.replicate_succ', cca2FlipLast_snoc, ← List.cons_append, List.getLastD_concat]

/-- **The attack against any fixed-length scheme.** Let `A = cca2Adversary` run with budget `2`
in `IND_b` under CCA2 with the key `k`. Suppose ciphertexts are nonempty and, for every challenge
`c = Enc_k(b^n)`, every decryption of `c` with its last bit flipped is a message `v` with
`⟨1, v⟩` ending in `!b`. Then `A` outputs `b` with probability one.

**Proof sketch.** Follow the three activations through `buildComp` and `simulate`.
1. On the empty log `A` asks `Challenge ⟨0^n, 1^n⟩`; the oracle samples `re`, answers
   `c = Enc_k(b^n)` (`cca2Messages_choice`) and records it.
2. On the one-entry log `A` asks `Dec` on `c'`, the flip of `c`; `c' ≠ c` (`cca2Alter_ne`), so
   CCA2's `Dec` samples `rd` and answers `⟨1, v⟩`.
3. On the two-entry log `A` outputs `¬(last bit of ⟨1, v⟩) = b`, within the budget.
Each sampled step is averaged by `expect_const`. -/
private theorem cca2Run (S : FixedLengthScheme) (n : ℕ) (hd : 0 < S.ctLen.eval n)
    (b : Bool) (k : List Bool)
    (hdec : ∀ (re : S.enc.Coins n) (rd : S.dec.Coins n), ∃ v : Fin n → Bool,
      decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn
        (cca2Alter (S.encryptAt n k (fun _ => b) re)))) rd) = some v ∧
      (List.ofFn (Fin.cons (α := fun _ => Bool) true v)).getLastD false = !b)
    (r : cca2Adversary.Coins n) :
    ProbComp.prob ((simulate (S.indImpl .cca2 b n k) (cca2Adversary.toComp (S.indCodec n) n 2 r)
      none).bind fun res => .pure (res.1 0)) (· = true) = if b = true then 1 else 0 := by
  obtain ⟨x, hx⟩ : ∃ x : (S.indSpec n).dom 2,
      x = cast (S.indSpec_challengeDom n).symm (cca2Messages n) := ⟨_, rfl⟩
  have h1 : (S.indCodec n).decodeMove
      (cca2Adversary.runAt n ((S.indCodec n).encodeLog []) r) = .query 2 x := by
    rw [MachineCodec.encodeLog_nil, cca2Adversary_run, if_pos rfl,
      FixedLengthScheme.indCodec_decodeMove]
    have hw : List.ofFn x = List.replicate n false ++ List.replicate n true := by
      rw [hx, cca2OfFn_cast (S.inLens_two n).symm, cca2Messages_ofFn]
    rw [← hw]
    exact decodeBitMove_query (S.inLens n) (S.outLens n) 1 2 x
  rw [NUPPT.toComp_eq, buildComp_succ_of_query (next := fun hist => (S.indCodec n).decodeMove
    (cca2Adversary.runAt n ((S.indCodec n).encodeLog hist) r)) h1, simulate_query,
    FixedLengthScheme.indImpl_challenge_none_onSpec]
  have hxc : cast (S.indSpec_challengeDom n) x = cca2Messages n := by
    rw [hx, cast_cast, cast_eq]
  simp only [hxc, cca2Messages_choice, OracleComp.bind_assoc, OracleComp.pure_bind,
    List.nil_append]
  rw [ProbComp.prob_bind]
  refine (congrArg (ProbComp.expect _) (funext fun re => ?_)).trans (ProbComp.expect_const _ _)
  have hne := cca2Alter_ne hd (S.encryptAt n k (fun _ => b) re)
  have h2 : (S.indCodec n).decodeMove (cca2Adversary.runAt n ((S.indCodec n).encodeLog
      [⟨2, x, cast (S.indSpec_challengeRng n).symm (S.encryptAt n k (fun _ => b) re)⟩]) r) =
      .query 1 (cast (S.indSpec_decDom n).symm
        (cca2Alter (S.encryptAt n k (fun _ => b) re))) := by
    simp only [MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
      FixedLengthScheme.indCodec_encodeEntry, cca2Adversary_one,
      FixedLengthScheme.indCodec_decodeMove]
    rw [cca2OfFn_cast (S.outLens_two n).symm, ← cca2Alter_ofFn hd,
      ← cca2OfFn_cast (S.inLens_one n).symm (S.indSpec_decDom n).symm]
    exact decodeBitMove_query (S.inLens n) (S.outLens n) 1 1 _
  rw [buildComp_succ_of_query (next := fun hist => (S.indCodec n).decodeMove
    (cca2Adversary.runAt n ((S.indCodec n).encodeLog hist) r)) h2, simulate_query,
    FixedLengthScheme.indImpl_dec_onSpec]
  have hcc : cast (S.indSpec_decDom n) (cast (S.indSpec_decDom n).symm
      (cca2Alter (S.encryptAt n k (fun _ => b) re))) =
        cca2Alter (S.encryptAt n k (fun _ => b) re) := by
    rw [cast_cast, cast_eq]
  have hopen : (FixedLengthScheme.decOpen .cca2
      (some (S.encryptAt n k (fun _ => b) re)).isSome && !decide
        (some (S.encryptAt n k (fun _ => b) re) =
          some (cca2Alter (S.encryptAt n k (fun _ => b) re)))) = true := by
    simp only [FixedLengthScheme.decOpen_cca2, Option.some.injEq,
      Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    exact fun h => hne h.symm
  rw [hcc, if_pos hopen]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind]
  rw [ProbComp.prob_bind]
  refine (congrArg (ProbComp.expect _) (funext fun rd => ?_)).trans (ProbComp.expect_const _ _)
  obtain ⟨v, hv, hlast⟩ := hdec re rd
  rw [hv, FixedLengthScheme.decAnswer_some]
  have h3 : (S.indCodec n).decodeMove (cca2Adversary.runAt n ((S.indCodec n).encodeLog
      ([⟨2, x, cast (S.indSpec_challengeRng n).symm (S.encryptAt n k (fun _ => b) re)⟩] ++
        [⟨1, cast (S.indSpec_decDom n).symm (cca2Alter (S.encryptAt n k (fun _ => b) re)),
          cast (S.indSpec_decRng n).symm (Fin.cons (α := fun _ => Bool) true v)⟩])) r) =
      .ret fun _ => b := by
    simp only [List.singleton_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
      FixedLengthScheme.indCodec_encodeEntry, cca2Adversary_two,
      FixedLengthScheme.indCodec_decodeMove]
    rw [cca2OfFn_cast (S.outLens_one n).symm, hlast, Bool.not_not]
    have hb : [b] = List.ofFn (fun _ : Fin 1 => b) := by
      rw [List.ofFn_const, List.replicate_one]
    rw [hb]
    exact decodeBitMove_ret (S.inLens n) (S.outLens n) 1 _
  rw [buildComp_zero_of_ret (next := fun hist => (S.indCodec n).decodeMove
    (cca2Adversary.runAt n ((S.indCodec n).encodeLog hist) r)) h3, simulate_pure,
    OracleComp.pure_bind, ProbComp.prob_pure]

/-- **Claim 169.a: the §3.9 scheme is not CCA2-secure** [PS10, §7.1.3, p. 169], whatever the
family `F`. Some adversary, with a constant query budget, has advantage `1` at every `n > 0`.

The source's attack asks `Dec` for "`c + 1`", the challenge plus one. Read as an exclusive-or with
a fixed nonzero string, it flips the last bit of the challenge. The result is a different, still
well-formed ciphertext, which CCA2's `Dec` therefore answers.

**Proof sketch.**
1. The machine `A` reads its log. With an empty log, it asks the challenge on `⟨0^n, 1^n⟩`. With
   one entry, the challenge answer `c`, it asks `Dec` on `c` with its last bit flipped. With two
   entries, the second a `Dec` answer `⟨v, m'⟩`, it outputs `¬ m'_{n-1}`. It is polynomial-time
   (`NUPPT.ofPolyTimeUniform`); its query budget is `2`, so the third activation's output is read.
2. In `IND_b` the challenge is `c = ⟨r, b^n ⊕ f_k(r)⟩`. For `n > 0` its last bit lies in the
   second component, so the flipped string `c'` is `⟨r, b^n ⊕ e_{n-1} ⊕ f_k(r)⟩`: well-formed,
   and not `c`. CCA2's `Dec` answers `⟨1, b^n ⊕ e_{n-1}⟩` (`runAt_prfDec`).
3. So, for every key and all coins, `A` outputs `b` (`cca2Run`): `IND_b` accepts with probability
   `1` if `b = 1` and `0` if `b = 0`, and the advantage is `|0 − 1| = 1`. -/
theorem prfFixedScheme_not_cca2 :
    ∃ (A : NUPPT) (q : PolyExpr), ∀ n, 0 < n →
      advantage ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) false n)
        ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) true n) = 1 := by
  refine ⟨cca2Adversary, .const 2, fun n hn => ?_⟩
  have hd : 0 < (prfFixedScheme F E hE hFE).ctLen.eval n := by
    rw [cca2CtLen]
    omega
  have hacc : ∀ b : Bool, accept ((prfFixedScheme F E hE hFE).indGame .cca2 cca2Adversary
      ((PolyExpr.const 2).eval n) b n) = if b = true then 1 else 0 := by
    intro b
    rw [PolyExpr.eval_const, accept_eq, FixedLengthScheme.indGame_eq, ProbComp.prob_bind]
    refine (congrArg (ProbComp.expect _) (funext fun rg => ?_)).trans (ProbComp.expect_const _ _)
    obtain ⟨kv, hk⟩ := cca2Gen F E hE hFE n rg
    rw [ProbComp.prob_bind]
    refine (congrArg (ProbComp.expect _) (funext fun r => ?_)).trans (ProbComp.expect_const _ _)
    rw [hk]
    refine cca2Run _ n hd b _ (fun re rd => ?_) r
    obtain ⟨xr, -, hc, -⟩ := cca2Cipher F E hE hFE n hn kv (fun _ => b) re
    refine ⟨cca2FlipBits (fun _ => b), ?_, cca2LastBit hn b⟩
    rw [hc, cca2Decrypt, cca2FlipBits_unmask]
  rw [advantage_eq, hacc, hacc]
  norm_num

/-- **The §3.9 scheme is not CCA2-secure** in the sense of Definition 168.1: an advantage equal
to `1` at every positive `n` is not negligible (Claim 169.a). -/
theorem not_prfFixedScheme_cca2 : ¬ (prfFixedScheme F E hE hFE).INDSecure .cca2 := by
  intro h
  rw [FixedLengthScheme.INDSecure_iff] at h
  obtain ⟨A, q, hA⟩ := prfFixedScheme_not_cca2 F E hE hFE
  obtain ⟨ε, hε, hle⟩ := h A q
  rw [negligible_iff] at hε
  obtain ⟨n₀, hn₀⟩ := hε 0
  have h1 := hn₀ (n₀ + 1) (by omega)
  have h2 := hle (n₀ + 1)
  rw [hA (n₀ + 1) (by omega)] at h2
  simp only [pow_zero, div_one] at h1
  linarith [le_abs_self (ε (n₀ + 1))]

end TCSlib.Cryptography.Composability
