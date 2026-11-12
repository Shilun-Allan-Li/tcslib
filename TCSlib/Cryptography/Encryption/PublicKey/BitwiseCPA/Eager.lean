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
may be sampled in advance (`expect_simulate_indImpl_cpa`, through the oracle equations
`indImpl_*_onSpec`, from `ChallengeSim.expect_simulate_eager`); and the padded encryptor of a padded public-key scheme pads the
original encryptor's output (`padded_enc_runAt`). All are read from the published lemmas of
`OracleSecurity` and `ChallengeSim`. The CPA game's codec is the bit codec of the scheme's
lengths by `AdaptiveCPA.indCodec_eq_bitCodec`, and casts are read by `AdaptiveCPA.ofFn_cast`.

## Main results

* `BitwiseSim.expect_simulate_indImpl_cpa`: eager challenge coins under CPA, for `indImpl`.
* `BitwiseSim.padded_enc_runAt`, `BitwiseSim.padded_enc_coins`: readers of the padded scheme.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 and §7.1.4, Definition 171.5 (book p. 171).
-/

namespace TCSlib.Cryptography.Composability.BitwiseSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim ProbComp

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

/-- The padded scheme's encryptor has the coin polynomial of the original encryptor:
`S.enc.coins = (S.padded L hL hmsg).enc.coins`. -/
theorem padded_enc_coins (S : PublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : S.enc.coins = (S.padded L hL hmsg).enc.coins := by
  rw [PublicKeyScheme.padded_enc, padEnc_coins]

end TCSlib.Cryptography.Composability.BitwiseSim
