/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import TCSlib.Cryptography.Asymptotic.Encryption
import TCSlib.Cryptography.Asymptotic.PRF

set_option maxHeartbeats 400000
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

variable (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G n s x))

/-- **The special encryption scheme** [PS10, Algorithm 157.2] as a `PrivateKeyScheme` with
`n`-bit messages, for a length-doubling family `G` with evaluator `E`: the key is `Gen`'s `n`
coins, `Enc` draws `r` as its `n` coins, and `Dec` is deterministic. -/
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
    have hk : (List.ofFn rg).length = n := by rw [List.length_ofFn]; rfl
    have hr : (List.ofFn re).length = n := by rw [List.length_ofFn]; rfl
    have hp : (E (pairEncode (List.ofFn rg) (List.ofFn re))).length = n + n := by
      rw [hGE n rg re, List.length_ofFn]
    rw [spDecStr_spEncStr E hk (by simp) hr hp, Option.getD_some]
    exact decodeFin_ofFn m

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
  sorry

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
  sorry

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
  sorry

end TCSlib.Cryptography.SecureComputation
