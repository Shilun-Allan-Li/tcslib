/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.Defs
import TCSlib.Cryptography.Asymptotic.MultiMessage
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
* `Composability.prfFixedScheme_not_cca2` (Claim 169.a, stated; a `sorry` under its sketch): an
  explicit adversary with advantage `1`.
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

/-- **Claim 169.a: the §3.9 scheme is not CCA2-secure** [PS10, §7.1.3, p. 169], whatever the
family `F`. Some adversary, with a constant query budget, has advantage `1` at every `n > 0`.

The source's attack asks `Dec` for "`c + 1`", the challenge plus one. Read as an exclusive-or with
a fixed nonzero string, it flips the last bit of the challenge. The result is a different, still
well-formed ciphertext, which CCA2's `Dec` therefore answers.

**Proof sketch.**
1. The machine `A` reads its log. With an empty log, it asks the challenge on `⟨0^n, 1^n⟩`. With
   one entry, the challenge answer `c`, it asks `Dec` on `c` with its last bit flipped. With two
   entries, the second a `Dec` answer `⟨v, m'⟩`, it outputs `¬ m'_{n-1}`. It is polynomial-time
   (`NUPPT.ofPolyTimeUniform`).
2. In `IND_b` the challenge is `c = ⟨r, b^n ⊕ f_k(r)⟩`. For `n > 0` its last bit lies in the
   second component, so the flipped string `c'` is `⟨r, b^n ⊕ e_{n-1} ⊕ f_k(r)⟩`: well-formed,
   and not `c`. CCA2's `Dec` answers `⟨1, b^n ⊕ e_{n-1}⟩` (`runAt_prfDec`).
3. So `A` outputs `b` with probability `1`, and the advantage is `|0 − 1| = 1`. -/
theorem prfFixedScheme_not_cca2 :
    ∃ (A : NUPPT) (q : PolyExpr), ∀ n, 0 < n →
      advantage ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) false n)
        ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) true n) = 1 := by
  sorry

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
