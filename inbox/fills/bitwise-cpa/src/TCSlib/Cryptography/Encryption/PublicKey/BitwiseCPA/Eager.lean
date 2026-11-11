/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Eager challenge coins and readers for the CPA game

Generic facts used by the hybrid argument for the bitwise scheme under chosen-plaintext attack
[PS10, p. 103, in the game of Definition 171.5]: under CPA the encryption coins of the challenge
may be sampled in advance (`expect_simulate_indImpl_cpa`, through the oracle equations `indImpl_*_onSpec`); resampling one coordinate of a
uniform tuple leaves it uniform (`expect_sample_update`); the CPA game's codec is the bit codec
of the scheme's lengths (`indCodec_eq_bitCodec`); and the padded encryptor of a padded public-key
scheme pads the original encryptor's output (`padded_enc_runAt`). All are read from the
published lemmas of `OracleSecurity`, `ChallengeSim` and `BitCodec`.

## Main results

* `BitwiseSim.expect_simulate_eager`, `expect_simulate_indImpl_cpa`: eager challenge coins under
  CPA, generically and for `indImpl`.
* `BitwiseSim.expect_sample_update`: resampling a coordinate.
* `BitwiseSim.indCodec_eq_bitCodec`, `BitwiseSim.padded_enc_runAt`: readers.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 and §7.1.4, Definition 171.5 (book p. 171).
-/

namespace TCSlib.Cryptography.Composability.BitwiseSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim ProbComp

/-- **Eager challenge coins, for any CPA-shaped oracle.** Let `impl` answer oracle `0`
all-`false`, a challenge from a recorded state `c` with `c`, and the first challenge `mm` by
sampling `re` and answering (and recording) `padFin d (g mm re)`; the state holds `d`-bit
strings, `d = outs 1`, read through the cast `e`. Then for every `G`,
`𝔼[G ∘ fst] (simulate impl c s) = 𝔼_{re} G (chRun (fun mm => g mm re) c (s.map (cast e))).1`.

**Proof sketch.** Substitute `d = outs 1`, so that the casts are identities. Induction on the
computation: decryption queries and repeated challenges are deterministic in both; at the first
challenge the lazy side samples `re` and continues from the recorded answer, by the induction
hypothesis an average over coins `re'` on which the recorded run does not depend
(`chRun_some_congr`), so `re'` marginalizes out (`expect_const`). -/
theorem expect_simulate_eager {ins outs : Fin 2 → ℕ} {d : ℕ} (hd : outs 1 = d)
    (e : (Fin d → Bool) = (Fin (outs 1) → Bool)) {R : Type} [Fintype R] [Nonempty R]
    (impl : QueryImpl (bitSpec ins outs) (Option (Fin d → Bool)) unifSpec)
    (g : (Fin (ins 1) → Bool) → R → List Bool)
    (h0 : ∀ x s, impl 0 x s = .pure (zeroBits _, s))
    (hrep : ∀ mm c, impl 1 mm (some c) = .pure (cast e c, some c))
    (hnew : ∀ mm, impl 1 mm none = (ProbComp.sample R).bind fun re =>
      .pure (cast e (padFin d (g mm re)), some (padFin d (g mm re))))
    {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α) (s : Option (Fin d → Bool)) :
    expect (simulate impl c s) (fun p => G p.1) =
      expect (ProbComp.sample R) fun re =>
        G (chRun (fun mm => g mm re) c (s.map (cast e))).1 := by
  subst hd
  have hc : ∀ x : Fin (outs 1) → Bool, cast e x = x := fun x => cast_eq e x
  have hmap : ∀ s : Option (Fin (outs 1) → Bool), s.map (cast e) = s := fun s => by
    cases s <;> simp
  simp only [hc] at hrep hnew
  simp only [hmap]
  induction c generalizing s with
  | pure a =>
    rw [simulate_pure, expect_pure]
    simp only [chRun_pure]
    exact (expect_const _ _).symm
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, h0, OracleComp.pure_bind]
      simp only [chRun_query_zero]
      exact ih _ s
    | 1, x, k, ih =>
      cases s with
      | some C =>
        rw [simulate_query, hrep, OracleComp.pure_bind]
        simp only [chRun_query_one_some]
        exact ih _ _
      | none =>
        rw [simulate_query, hnew, OracleComp.bind_assoc, expect_bind]
        refine congrArg _ (funext fun re => ?_)
        rw [OracleComp.pure_bind, ih, chRun_query_one_none]
        dsimp only
        exact (congrArg _ (funext fun re' =>
          congrArg (fun p : α × Option (Fin (outs 1) → Bool) => G p.1)
            (chRun_some_congr (fun mm => g mm re') (fun mm => g mm re) _ _))).trans
          (expect_const _ _)

/-- **Eager challenge coins under CPA.** Simulating the oracles of `Ind_b` from the unchallenged
state has, for every `G`, the expectation of first sampling the encryption coins `re` and then
running the deterministic oracles whose challenge `mm` is answered with `Enc(⟨pk, m_b⟩; re)`,
the halves read through `indSpec_challengeDom`:
`𝔼[G ∘ fst] (simulate (indImpl .cpa b n pk sk) c none) = 𝔼_{re} G (chRun g_re c none).1`.

**Proof sketch.** `expect_simulate_eager` with `d = ctLen(n)` (`outLens_one`), the cast
`indSpec_challengeRng`, and the oracle equations `indImpl_dec_onSpec` (with `decOpen_cpa`),
`indImpl_challenge_repeat_onSpec` and `indImpl_challenge_none_onSpec`. -/
theorem expect_simulate_indImpl_cpa (S : FixedLengthPKScheme) (b : Bool) (n : ℕ)
    (pk sk : List Bool) {α : Type} (G : α → ℝ) (c : OracleComp (S.indSpec n) α) :
    expect (simulate (S.indImpl .cpa b n pk sk) c none) (fun p => G p.1) =
      expect (ProbComp.sample (S.enc.Coins n)) fun re =>
        G (chRun (fun mm => S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).2
            else (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).1))) re)
          c none).1 :=
  expect_simulate_eager (S.outLens_one n) (S.indSpec_challengeRng n).symm _ _
    (fun x s => by
      rw [S.indImpl_dec_onSpec]
      simp only [FixedLengthScheme.decOpen_cpa, Bool.false_and, Bool.false_eq_true, if_false])
    (fun mm C => S.indImpl_challenge_repeat_onSpec .cpa b n pk sk mm C)
    (fun mm => S.indImpl_challenge_none_onSpec .cpa b n pk sk mm) G c none

/-- `List.ofFn` does not see a cast between equal lengths:
`List.ofFn (cast h f) = List.ofFn f` for `h : (Fin a → Bool) = (Fin b → Bool)` and `a = b`. -/
theorem ofFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
  subst hab
  rfl

/-- **Resampling one coordinate of a uniform tuple leaves it uniform**:
`𝔼_{v} 𝔼_{b} f (update v j b) = 𝔼_{v} f v`.

**Proof sketch.** The map `(v, b) ↦ (update v j b, v j)` is an involution of
`(ι → β) × β` (`Function.update_idem`, `Function.update_eq_self`); reindexing the product sample
along it (`expect_sample_equiv`, `expect_sample_prod`) turns the left side into
`𝔼_{v} 𝔼_{b} f v = 𝔼_{v} f v` (`expect_const`). -/
theorem expect_sample_update {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    (j : ι) (f : (ι → β) → ℝ) :
    (expect (sample (ι → β)) fun v => expect (sample β) fun b => f (Function.update v j b)) =
      expect (sample (ι → β)) f := by
  let e : (ι → β) × β ≃ (ι → β) × β :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  rw [← expect_sample_prod (fun p : (ι → β) × β => f (Function.update p.1 j p.2))]
  have h := expect_sample_equiv e (fun p : (ι → β) × β => f p.1)
  refine h.trans ?_
  rw [expect_sample_prod]
  exact congrArg _ (funext fun v => expect_const (sample β) (f v))

/-- **The CPA game's codec is the bit codec of the scheme's lengths**:
`S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1`.

**Proof sketch.** Both are structures with the same three fields
(`indCodec_decodeMove`, `indCodec_encodeEntry`, `indCodec_timeout` and the `bitCodec` readers). -/
theorem indCodec_eq_bitCodec (S : FixedLengthPKScheme) (n : ℕ) :
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

/-- **The padded encryptor pads the original encryptor's output**: for a padded public-key
scheme, `Enc'(1^n, y; r) = padCt L(n) (Enc(1^n, y; r))`, with the coin string read as a list
(`PublicKeyScheme.padded_enc`, `runAt_padEnc`, `NUPPT.coinsCongr_ofFn`). -/
theorem padded_enc_runAt (S : PublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) (n : ℕ) (y : List Bool)
    (r : (S.padded L hL hmsg).enc.Coins n) :
    (S.padded L hL hmsg).enc.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
  have key : ∀ E : NUPPT, E = padEnc S.enc L → ∀ r : E.Coins n,
      E.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
    rintro E rfl r
    rw [runAt_padEnc S.enc_uniform L n y r, NUPPT.runAt_eq, NUPPT.coinsCongr_ofFn]
  exact key _ (PublicKeyScheme.padded_enc S L hL hmsg) r

/-- The padded scheme's encryptor has the coin polynomial of the original encryptor. -/
theorem padded_enc_coins (S : PublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : S.enc.coins = (S.padded L hL hmsg).enc.coins := by
  rw [PublicKeyScheme.padded_enc, padEnc_coins]

end TCSlib.Cryptography.Composability.BitwiseSim
