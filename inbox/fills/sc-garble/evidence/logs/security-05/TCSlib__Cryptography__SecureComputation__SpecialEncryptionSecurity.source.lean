/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.Pad
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.WrongKey
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The special encryption scheme of Yao's protocol: security (statement phase)

[PS10, Algorithm 157.2] as a `PrivateKeyScheme`, and Claim 157.a (inventory): the scheme is
multi-message secure, and a ciphertext decrypted under an independent key gives `⊥` except with
negligible probability ([PS10, §6.2.2], "the extra property"). The algorithms are in
`SpecialEncryption.lean`.

**The length-doubling PRF.** It is a keyed family with `n`-bit keys and inputs and `2n`-bit
outputs, pseudorandom as an oracle ensemble against random functions with `2n`-bit outputs
(`PRFOut`). This is the ch. 2–4 layer's Definition 96.2 (`PRF`) with the output length a
parameter; `OracleEnsemble.keyed` already allows any output length.

## Main definitions

* `SecureComputation.PRFOut`: a pseudorandom function family with `ℓ₂(n)`-bit outputs.
* `SecureComputation.specialScheme`: Algorithm 157.2 as a `PrivateKeyScheme` (`n`-bit messages),
  correctness proved.

## Main results

* `SecureComputation.specialScheme_multiMessageSecure`, `spDecStr_wrongKey`,
  `specialScheme_wrongKey` (Claim 157.a, stated; `sorry`s under sketches).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Algorithm 157.2 (book pp. 156–157), and Definitions 93.1 and 96.2.
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-! ### Pseudorandom functions with any output length -/

/-- **A pseudorandom function family with `ℓ₂(n)`-bit outputs** [PS10, Definition 96.2, with the
output length a parameter]: keys and inputs of `n` bits. (1) A polynomial-time evaluator `E`
computes `f_s(x)` from `⟨s, x⟩`. (2) The keyed ensemble `{s ← U_n : f_s}` is
oracle-indistinguishable from the random functions `{0,1}^n → {0,1}^{ℓ₂(n)}`. With `ℓ₂ = n + n`
it is the source's length-doubling family. -/
structure PRFOut (ℓ₂ : PolyExpr)
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)) : Prop where
  /-- Clause (1): `f_s(x)` is polynomial-time computable from `⟨s, x⟩`. -/
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x)
  /-- Clause (2): `{s ← U_n : f_s} ≈ {F ← RF : F}` as oracle ensembles. -/
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) G).Indist
    (OracleEnsemble.random .var ℓ₂)

/-- With `n`-bit outputs, `PRFOut` is the ch. 2–4 layer's `PRF` (duplication-ledger item DL-8:
`PRFOut` generalizes `PRF`, and agrees with it at `ℓ₂ = n`). -/
theorem prfOut_var_iff (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) :
    PRFOut .var F ↔ PRF F :=
  ⟨fun h => ⟨h.easy, h.pseudorandom⟩, fun h => ⟨h.easy, h.pseudorandom⟩⟩

variable (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G n s x))

/-- **The special encryption scheme** [PS10, Algorithm 157.2] as a `PrivateKeyScheme` with
`n`-bit messages, for a length-doubling family `G` with evaluator `E`: the key is `Gen`'s `n`
coins, `Enc` draws `r` as its `n` coins, and `Dec` is deterministic. -/
@[simps (config := { isSimp := false }) gen enc dec]
noncomputable def specialScheme : PrivateKeyScheme where
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  enc := NUPPT.ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var
  dec := NUPPT.ofPolyTimeUniform (polyTimeComputable_spDecFun hE) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    rw [runAt_coinKey, runAt_spEnc hE, runAt_spDec hE]
    have hk : (List.ofFn rg).length = n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_var]
    have hr : (List.ofFn re).length = n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_var]
    have hp : (E (pairEncode (List.ofFn rg) (List.ofFn re))).length = n + n := by
      have hrg := (List.length_ofFn (f := rg)).symm.trans hk
      have hre := (List.length_ofFn (f := re)).symm.trans hr
      rw [List.ofFn_congr hrg rg, List.ofFn_congr hre re, hGE, List.length_ofFn]
    rw [spDecStr_spEncStr E hk (by simp) hr hp, Option.getD_some]
    exact decodeFin_ofFn m

/-- The key generator of `specialScheme` outputs its coins: `Gen(1^n; rg) = ⟦rg⟧`. -/
theorem specialScheme_gen_runAt (n : ℕ) :
    ∀ rg : (specialScheme G E hE hGE).gen.Coins n,
      (specialScheme G E hE hGE).gen.runAt n [] rg = List.ofFn rg := by
  rw [specialScheme_gen]
  intro rg
  exact runAt_coinKey .var n rg

/-- The encryption machine uses its coins as the nonce:
`(specialScheme G E hE hGE).enc.runAt n ⟨k,m⟩ re = spEncStr E k m ⟦re⟧`. -/
theorem specialScheme_enc_runAt (n : ℕ) :
    ∀ (k m : List Bool) (re : (specialScheme G E hE hGE).enc.Coins n),
      (specialScheme G E hE hGE).enc.runAt n (pairEncode k m) re =
        spEncStr E k m (List.ofFn re) := by
  rw [specialScheme_enc]
  intro k m re
  exact runAt_spEnc hE .var n k m re

/-- The key coins of `specialScheme` as an `n`-bit key, keeping the string. -/
noncomputable def specialScheme_keyCoinsEquiv (n : ℕ) :
    (specialScheme G E hE hGE).gen.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [specialScheme_gen]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- `⟦specialScheme_keyCoinsEquiv n rg⟧ = ⟦rg⟧`. -/
theorem specialScheme_keyCoinsEquiv_ofFn (n : ℕ) (rg : (specialScheme G E hE hGE).gen.Coins n) :
    List.ofFn (specialScheme_keyCoinsEquiv G E hE hGE n rg) = List.ofFn rg := by
  rw [specialScheme_keyCoinsEquiv, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-- The encryption coins of `specialScheme` as an `n`-bit nonce, keeping the string. -/
noncomputable def specialScheme_nonceCoinsEquiv (n : ℕ) :
    (specialScheme G E hE hGE).enc.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [specialScheme_enc]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- `⟦specialScheme_nonceCoinsEquiv n re⟧ = ⟦re⟧`. -/
theorem specialScheme_nonceCoinsEquiv_ofFn (n : ℕ) (re : (specialScheme G E hE hGE).enc.Coins n) :
    List.ofFn (specialScheme_nonceCoinsEquiv G E hE hGE n re) = List.ofFn re := by
  rw [specialScheme_nonceCoinsEquiv, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-! ### Claim 157.a -/

/-- **Claim 157.a (i): the special scheme is multi-message secure** [PS10, §6.2.2, "it is easy to
modify construction 99.1"] when `G` is a length-doubling PRF.

**Proof sketch.** As [PS10, Theorem 99.2] for Algorithm 99.1 (`prfScheme_multiMessageSecure`):
replace `f_k` by a random function with `2n`-bit outputs (PRF security, one oracle query per
ciphertext); then the pads of distinct `r`'s are independent uniform `2n`-bit strings, so the
ciphertexts are independent of the messages unless two `r`'s collide, with probability at most
`C(q(n)+1, 2) · 2^{-n}`. The zero prefix `0^n` is masked like the message. -/
theorem specialScheme_multiMessageSecure (hG : PRFOut (.add .var .var) G) :
    (specialScheme G E hE hGE).MultiMessageSecure := by
  rw [PrivateKeyScheme.multiMessageSecure_iff]
  intro D q
  obtain ⟨ε, hε, hb⟩ := MultiMsg.exists_negligible_distAdv_prfEncRealOut
    hG.pseudorandom D q
  refine ⟨ε, hε, fun n m m' => ?_⟩
  let e : (specialScheme G E hE hGE).gen.Coins n ×
      (Fin (q.eval n + 1) → (specialScheme G E hE hGE).enc.Coins n) ≃
      (Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) :=
    (specialScheme_keyCoinsEquiv G E hE hGE n).prodCongr
      (Equiv.piCongrRight fun _ => specialScheme_nonceCoinsEquiv G E hE hGE n)
  have hX : ∀ v : Fin (q.eval n + 1) → Fin n → Bool,
      (specialScheme G E hE hGE).multiEncDist n (q.eval n) v =
        fun t => encodeTupleOut (prfEncRealOut (G n)
          (fun i => Fin.append (fun _ : Fin n => false) (v i)) (e t)) := by
    intro v
    funext t
    rw [PrivateKeyScheme.multiEncDist_apply, encodeTupleOut_eq]
    refine congrArg PrivateKeyScheme.encodeList (congrArg List.ofFn (funext fun i => ?_))
    rw [specialScheme_gen_runAt, specialScheme_enc_runAt, prfEncRealOut_apply]
    simp only [e, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Equiv.piCongrRight_apply, Pi.map_apply]
    rw [← specialScheme_keyCoinsEquiv_ofFn G E hE hGE n t.1,
      ← specialScheme_nonceCoinsEquiv_ofFn G E hE hGE n (t.2 i)]
    rw [spEncStr_eq_zeroPrefixMask E _ _ _ (by rw [hGE]; simp), hGE,
      ← zipWith_xor_ofFn_add, List.ofFn_fin_append, List.ofFn_const, List.length_ofFn]
  rw [distAdv_def, hX m, hX m',
    acceptProb_comp_equiv e (fun z => encodeTupleOut (prfEncRealOut (G n)
      (fun i => Fin.append (fun _ : Fin n => false) (m i)) z)),
    acceptProb_comp_equiv e (fun z => encodeTupleOut (prfEncRealOut (G n)
      (fun i => Fin.append (fun _ : Fin n => false) (m' i)) z)), ← distAdv_def]
  exact hb n _ _

/-- **Claim 157.a (ii), on strings: a wrong key gives `⊥`** [PS10, §6.2.2, "the extra property"]
for any polynomial message length `ℓ`: for `G` a PRF with `n + ℓ(n)`-bit outputs and every
`ℓ(n)`-bit message, encrypting under `k` and decrypting under an independent `k'` gives `⊥`
except with negligible probability.

**Proof sketch.** Decryption under `k'` succeeds only if `f_k(r)_{<n} = f_{k'}(r)_{<n}`. The
distinguisher with oracle `O` samples `k'` and `r`, queries `O(r)`, and accepts iff the first `n`
bits agree with `f_{k'}(r)`. Against a random function this has probability `2^{-n}`, so against
`f_k` it has probability at most `2^{-n}` plus the PRF advantage: negligible. The guard does not
fire on honest ciphertexts. -/
theorem spDecStr_wrongKey (ℓ : PolyExpr)
    (G' : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))
    (E' : List Bool → List Bool)
    (hGE' : ∀ n (s x : Fin n → Bool), E' (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G' n s x))
    (hG' : PRFOut (.add .var ℓ) G') :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m : Fin (ℓ.eval n) → Bool),
      1 - ε n < uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        spDecStr E' n (ℓ.eval n) (List.ofFn t.2.1)
          (spEncStr E' (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2)) = none) := by
  obtain ⟨E₀, hE₀, hGE₀⟩ := hG'.easy
  obtain ⟨ε, hε, hb⟩ := SpecialWrongKey.exists_negligible_prefix_collision
    ℓ G' E₀ hE₀ hGE₀ hG'.pseudorandom
  refine ⟨fun n => ε n + (2 : ℝ)⁻¹ ^ n, hε.add negligible_two_pow_neg, fun n m => ?_⟩
  have hevent :
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        spDecStr E' n (ℓ.eval n) (List.ofFn t.2.1)
          (spEncStr E' (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2)) = none) =
        1 - uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
          (List.ofFn (G' n t.1 t.2.2)).take n =
            (List.ofFn (G' n t.2.1 t.2.2)).take n) := by
    rw [OneWay.uprob_congr (fun t :
        (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
      SpecialWrongKey.spDecStr_none_iff_prefix_ne
      (G' n) E' (hGE' n) t.1 t.2.1 t.2.2 m), uprob_not]
  rw [hevent]
  have hpos : 0 < (2 : ℝ)⁻¹ ^ n := pow_pos (by norm_num) n
  have hbound := hb n
  dsimp only
  linarith

/-- **Claim 157.a (ii) for the scheme**: under an independent key, `Dec` returns `⊥` (an output
that decodes to no `n`-bit message) except with negligible probability, the source's
`Pr[k, k' ← Gen(1^n), c ← Enc_k(m) : Dec_{k'}(c) = ⊥] > 1 − ε(n)`.

**Proof sketch.** `runAt_spEnc` and `runAt_spDec` reduce it to `spDecStr_wrongKey` at `ℓ = n`;
the `⊥` string `1^{n+1}` decodes to no `n`-bit message, and a `some` output has `n` bits. -/
theorem specialScheme_wrongKey (hG : PRFOut (.add .var .var) G) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m : Fin n → Bool),
      1 - ε n < uprob (fun t : (specialScheme G E hE hGE).gen.Coins n ×
          (specialScheme G E hE hGE).gen.Coins n × (specialScheme G E hE hGE).enc.Coins n ×
          (specialScheme G E hE hGE).dec.Coins n =>
        decodeFin n ((specialScheme G E hE hGE).dec.runAt n
          (pairEncode ((specialScheme G E hE hGE).gen.runAt n [] t.2.1)
            ((specialScheme G E hE hGE).enc.runAt n
              (pairEncode ((specialScheme G E hE hGE).gen.runAt n [] t.1) (List.ofFn m)) t.2.2.1))
          t.2.2.2) = none) := by
  obtain ⟨ε, hε, hb⟩ := spDecStr_wrongKey .var G E hGE hG
  refine ⟨ε, hε, fun n m => ?_⟩
  let K := Fin n → Bool
  let ek := specialScheme_keyCoinsEquiv G E hE hGE n
  let er := specialScheme_nonceCoinsEquiv G E hE hGE n
  let e : (specialScheme G E hE hGE).gen.Coins n ×
      (specialScheme G E hE hGE).gen.Coins n ×
      (specialScheme G E hE hGE).enc.Coins n × (specialScheme G E hE hGE).dec.Coins n ≃
      (K × K × K) × (specialScheme G E hE hGE).dec.Coins n :=
    { toFun := fun t => ((ek t.1, ek t.2.1, er t.2.2.1), t.2.2.2)
      invFun := fun t => (ek.symm t.1.1, ek.symm t.1.2.1, er.symm t.1.2.2, t.2)
      left_inv := by intro t; simp
      right_inv := by intro t; simp }
  have hk : ∀ k : K, List.ofFn (ek.symm k) = List.ofFn k := by
    intro k
    simpa only [Equiv.apply_symm_apply] using
      (specialScheme_keyCoinsEquiv_ofFn G E hE hGE n (ek.symm k)).symm
  have hr : ∀ r : K, List.ofFn (er.symm r) = List.ofFn r := by
    intro r
    simpa only [Equiv.apply_symm_apply] using
      (specialScheme_nonceCoinsEquiv_ofFn G E hE hGE n (er.symm r)).symm
  refine (hb n m).trans_le ?_
  rw [PolyExpr.eval_var]
  rw [← uprob_comp_equiv e.symm]
  rw [← uprob_fst (β := (specialScheme G E hE hGE).dec.Coins n)
    (fun t : K × K × K => spDecStr E n n (List.ofFn t.2.1)
      (spEncStr E (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2)) = none)]
  apply uprob_mono
  intro t ht
  rw [specialScheme_gen_runAt, specialScheme_gen_runAt, specialScheme_enc_runAt,
    runAt_spDec hE]
  change decodeFin n ((spDecStr E n n (List.ofFn (ek.symm t.1.2.1))
    (spEncStr E (List.ofFn (ek.symm t.1.1)) (List.ofFn m)
      (List.ofFn (er.symm t.1.2.2)))).getD (true :: List.replicate n true)) = none
  rw [hk, hk, hr, ht, Option.getD_none, decodeFin_eq, dif_neg (by simp)]

end TCSlib.Cryptography.SecureComputation
