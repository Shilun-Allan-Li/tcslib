/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Readers of the padded encryptor for the CPA game

Facts used by the hybrid argument for the bitwise scheme under chosen-plaintext attack
[PS10, p. 103, in the game of Definition 171.5]: the padded encryptor of a padded public-key
scheme pads the original encryptor's output (`padded_enc_runAt`) and has its coins
(`padded_enc_coins`). Both are read from the published lemmas of `OracleSecurity`. Eager challenge
coins under CPA are `expect_simulate_indImpl_cpa` (`OracleSecurity`).

## Main results

* `BitwiseSim.padded_enc_runAt`, `BitwiseSim.padded_enc_coins`: readers of the padded scheme.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 and §7.1.4, Definition 171.5 (book p. 171).
-/

namespace TCSlib.Cryptography.Composability.BitwiseSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim ProbComp

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
