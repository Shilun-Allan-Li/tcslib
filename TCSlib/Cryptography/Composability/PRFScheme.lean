/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.Defs
import TCSlib.Cryptography.Asymptotic.MultiMessage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The §3.9 scheme is CPA- and CCA1-secure (statement phase)

[PS10, Theorem 168.2]: the scheme of Algorithm 99.1 (the ch. 2–4 layer's `prfScheme`:
`Enc_k(m) = ⟨r, m ⊕ f_k(r)⟩` for a fresh uniform `r`) is CPA- and CCA1-secure when `F` is a PRF.

## Main definitions

* `Composability.prfFixedScheme`: `prfScheme`, whose ciphertexts have `3n + 2` bits.

## Main results

* `Composability.prfFixedScheme_cpa`, `Composability.prfFixedScheme_cca1` (Thm 168.2, stated;
  `sorry`s under the source's sketch).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 99.1 and Theorem 168.2 (book pp. 99, 168; the theorem calls it "construction 99.1").
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
    intro n rg m r
    show ((NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var).runAt n
      (pairEncode ((NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var).runAt n [] rg)
        (List.ofFn m)) r).length = _
    rw [runAt_coinKey, runAt_prfEnc hE]
    have h : E (pairEncode (List.ofFn rg) (List.ofFn r)) = List.ofFn (F n rg r) := hFE n rg r
    rw [h, length_pairEncode]
    have hc : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) PolyExpr.var).coinLen n
        = n := rfl
    simp
    omega

/-- **Theorem 168.2 (CPA)** [PS10]: if `F` is a pseudorandom function family, the §3.9 scheme is
CPA-secure.

**Proof sketch** (the source's).
1. Replace `f_k` by a random function: by PRF security, the advantage changes by a negligible
   amount (the reduction answers `Enc` and the challenge by querying its own oracle at the fresh
   `r`; efficiency by T1).
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
queries before the challenge with its oracle (`Dec_k(⟨r, c⟩) = c ⊕ f_k(r)`). The bad event adds
the case that a pre-challenge decryption query used the challenge's `r*`, again at most
`q(n)/2^n`, because `r*` is drawn after those queries. -/
theorem prfFixedScheme_cca1 (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cca1 := by
  sorry

end TCSlib.Cryptography.Composability
