/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bitwise scheme under chosen-plaintext attack

The bitwise scheme of [PS10, p. 103] encrypts an `n`-bit message one bit at a time with a
single-bit scheme (such as the trapdoor scheme of Algorithm 104.3, secure by Theorem 104.4).
Padded to fixed-length ciphertexts (`PublicKeyScheme.padded`), it is a fixed-length scheme with
`n`-bit messages. If the single-bit scheme is secure, the padded bitwise scheme is CPA-secure in
the game of [PS10, Definition 171.5], where the adversary chooses its two messages after seeing
the public key, and hence secure in the adaptive multi-challenge game.

Ensemble security of the bitwise scheme for message pairs fixed in advance
(`BitPublicKeyScheme.SingleBitSecure.bitwise`) is not enough here: there the messages cannot
depend on the public key. The proof below therefore goes back to single-bit security.

## Main results

* `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa` (stated; a `sorry` under its sketch):
  the padded bitwise scheme is CPA-secure.
* `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_adaptive_cpa`: and adaptively CPA-secure.
* `BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa`: a fixed-length scheme with `n`-bit
  messages and the same key generator is adaptively CPA-secure.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 (the bitwise scheme and the hybrid argument); Algorithm 104.3 and Theorem 104.4 (the
  single-bit trapdoor scheme, book pp. 104–105); Definition 171.5 (book p. 171).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- **The padded bitwise scheme is CPA-secure** when its single-bit scheme is secure
[PS10, the hybrid argument of p. 103, in the CPA game of Definition 171.5]. The bound `hL`
covers every ciphertext of the bitwise scheme, so `S.bitwise.padded L hL hmsg` has `n`-bit
messages and `L(n)`-bit ciphertexts.

**Proof sketch.**
1. Fix `A` and `q`. For `j ≤ n` let `H_j` be the CPA experiment whose challenge encrypts, bit by
   bit with independent coins, the first `j` bits of the right message and the remaining bits of
   the left message; `H_0` and `H_n` are the experiments with `b = false` and `b = true`.
2. By `Games.exists_advantage_hybrid_gap`, at each `n > 0` some `j⋆(n) < n` has
   `advantage(H_{j⋆}, H_{j⋆+1}) ≥ advantage(H_0, H_n) / n`; at `n = 0` the messages are empty and
   the advantage is `0`.
3. `H_{j⋆}` and `H_{j⋆+1}` differ only in the plaintext bit of block `j⋆`. As in
   `BitPublicKeyScheme.SingleBitSecure.padded_cpa`, the distinguisher `D` on `⟨pk, c⟩` runs `A` on
   `pk`, answers the challenge `⟨m₀, m₁⟩` with the padded bitwise ciphertext whose block `j⋆` is
   `c` and whose other blocks it encrypts itself (bits of `m₁` before `j⋆`, of `m₀` after) on
   `pk` and its own coins, and outputs `A`'s bit, flipped when `(m₀_{j⋆}, m₁_{j⋆}) = (1, 0)` and
   replaced by `0` when the two bits agree or no challenge was asked. Then
   `advantage(H_{j⋆}, H_{j⋆+1})` equals `D`'s single-bit advantage between `⟨pk, Enc_pk(0)⟩` and
   `⟨pk, Enc_pk(1)⟩` exactly (the first-challenge congruence and eager coins of `padded_cpa`). `D`
   is a non-uniform PPT by `Games.exists_handlerMachine` (T1), with `j⋆(n)` in the handler's
   initial state and `n` single-bit encryption tapes as its seed; the bitwise ciphertext layout is
   read through `bitwise_enc_runAt` and `bitwiseEncCoins_ofFn`.
4. So `A`'s advantage is at most `n` times a negligible function (`singleBitSecure_iff`),
   negligible by `Negligible.polyExpr_mul` with `PolyExpr.var`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).INDSecure .cpa := by
  sorry

/-- **The padded bitwise scheme is adaptively CPA-secure** when its single-bit scheme is secure:
`bitwise_padded_cpa` followed by the hybrid lifting
`Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_adaptive_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).AdaptiveINDSecure .cpa :=
  (h.bitwise_padded_cpa L hL hmsg).adaptive_cpa

/-- **A secure single-bit scheme yields an adaptively CPA-secure scheme with `n`-bit messages**:
some fixed-length scheme with message length `PolyExpr.var` and the same key generator is
secure in the adaptive multi-challenge CPA game. The padding bound comes from
`PublicKeyScheme.exists_padBound`.

**Proof sketch.** Take `L`, `hL` and `hmsg` from `S.bitwise.exists_padBound`; the witness is
`S.bitwise.padded L hL hmsg` (`PublicKeyScheme.padded_msgLen`, `PublicKeyScheme.padded_gen`, and
the generator of `S.bitwise` is `S.gen`), secure by `bitwise_padded_adaptive_cpa`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) :
    ∃ S' : FixedLengthPKScheme, S'.msgLen = .var ∧ S'.gen = S.gen ∧
      S'.AdaptiveINDSecure .cpa := by
  obtain ⟨L, hL, hmsg⟩ := S.bitwise.exists_padBound
  exact ⟨S.bitwise.padded L hL hmsg, PublicKeyScheme.padded_msgLen _ _ _ _,
    (PublicKeyScheme.padded_gen _ _ _ _).trans (BitPublicKeyScheme.bitwise_gen S),
    h.bitwise_padded_adaptive_cpa L hL hmsg⟩

end TCSlib.Cryptography.Composability
