/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.Entropy
import TCSlib.InformationTheory.Extractors
import TCSlib.Cryptography.Asymptotic.Adversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# No efficient one-bit extractor for efficient sources (statement phase)

[PS10, Theorem 183.6]: let `C` be the set of all efficiently computable `(n − 2)`-sources on
`{0,1}^n`; then there is no 1-bit `1/4`-extractor for `C`.

**The source's proof.** Suppose `Ext` is a `1/4`-extractor for `C`. Since `U_n ∈ C`,
`Pr[Ext(U_n) = 1] ≥ 1/4`, so `S = {x : Ext(x) = 1}` has at least `2^{n−2}` elements. The source
`X` samples `x ← U_n` until `Ext(x) = 1`, giving up after 10 tries with a fresh `x ← U_n`. It is a
mixture of `U_n` and the flat source on `S`, both `(n − 2)`-sources, so it is one. It is efficient
because `Ext` is. And `Pr[Ext(X) = 1] ≥ 1 − (3/4)^{10} > 0.9`, so `Ext(X)` is not `1/4`-close to
`U_1`.

**Source gap (inventory Thm-183.6).** "`X` is computable in polynomial time since `Ext` is" needs
`Ext` to be efficient, so the theorem is stated for polynomial-time `Ext`.

**The formal reading.**
- A source at `n` is efficient when it is the law of `padFin n (S(1^n))` for a uniform PPT `S`,
  over `S`'s uniform coins (`samplerLaw`).
- The class `C` at `n` is the set of efficient laws that are `(n − 2)`-sources (`effSources`).
- The extractor property is P0's `IsExtractor` ([PS10, Def 181.2]).
- The theorem is stated at **every** `n`: for every polynomial-time `Ext` and every `n`, the
  `1`-bit function `Ext` induces on `n`-bit strings is not a `1/4`-extractor for `C` at `n`. The
  witness depends on `n`: `U_n` if `Ext` fails on it, and otherwise the source's `X`. This is
  stronger than the source's "there is no extractor", which needs only one `n`. For `n ≤ 2` it is
  trivial, since every distribution is a `(n − 2)`-source there (a point mass is a witness); the
  content is at `n ≥ 3`.

## Main definitions

* `Randomness.samplerLaw`: the law of a machine's `n`-bit output.
* `Randomness.effSources`: the efficiently samplable `k`-sources at `n`.
* `Randomness.extBit`: the `1`-bit function induced on `n`-bit strings by a string function.

## Main results

* `Randomness.not_isExtractor_effSources` (Thm 183.6, stated; a `sorry` under the source's
  sketch).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.3.2, Definition 183.5 and Theorem 183.6 (book pp. 183–184).
-/

namespace TCSlib.Cryptography.Randomness

open Complexity TCSlib.Cryptography TCSlib.InformationTheory

/-- **The law of a sampler's `n`-bit output**: the distribution of `padFin n (S(1^n; r))` for
uniform coins `r`. -/
noncomputable def samplerLaw (S : NUPPT) (n : ℕ) : FinDist (Fin n → Bool) :=
  (FinDist.uniform (S.Coins n)).map fun r => padFin n (S.runAt n [] r)

/-- The probability of an `n`-bit word under `samplerLaw S n` is the sum of the uniform
coin probabilities over tapes whose padded sampler output is that word. -/
theorem samplerLaw_apply (S : NUPPT) (n : ℕ) (x : Fin n → Bool) :
    (samplerLaw S n).prob x =
      ∑ r ∈ (Finset.univ : Finset (S.Coins n)).filter
        (fun r => padFin n (S.runAt n [] r) = x), (Fintype.card (S.Coins n) : ℝ)⁻¹ := by
  rw [samplerLaw, FinDist.map_apply]
  simp only [FinDist.uniform_apply]

/-- The probability field of `samplerLaw S n` maps each word to the sum of the uniform
coin probabilities over its preimage under the padded sampler output. -/
theorem samplerLaw_prob (S : NUPPT) (n : ℕ) :
    (samplerLaw S n).prob = fun x =>
      ∑ r ∈ (Finset.univ : Finset (S.Coins n)).filter
        (fun r => padFin n (S.runAt n [] r) = x), (Fintype.card (S.Coins n) : ℝ)⁻¹ :=
  funext (samplerLaw_apply S n)

/-- **The efficiently samplable `k(n)`-sources at `n`** [PS10, Theorem 183.6, "efficiently
computable sources"]: the laws of uniform PPT samplers that are `k(n)`-sources. -/
def effSources (k : ℕ → ℝ) (n : ℕ) : Set (FinDist (Fin n → Bool)) :=
  {X | ∃ S : NUPPT, S.Uniform ∧ X = samplerLaw S n ∧ FinDist.IsSource (k n) X}

/-- A distribution belongs to `effSources k n` exactly when it is the law of a uniform PPT
sampler and is a `k(n)`-source. -/
theorem effSources_iff (k : ℕ → ℝ) (n : ℕ) (X : FinDist (Fin n → Bool)) :
    X ∈ effSources k n ↔
      ∃ S : NUPPT, S.Uniform ∧ X = samplerLaw S n ∧ FinDist.IsSource (k n) X := Iff.rfl

/-- The `1`-bit function induced on `n`-bit strings by a string function: the first bit of its
output (`padFin 1`). -/
def extBit (Ext : List Bool → List Bool) (n : ℕ) : (Fin n → Bool) → (Fin 1 → Bool) :=
  fun x => padFin 1 (Ext (List.ofFn x))

/-- On an `n`-bit input `x`, `extBit Ext n` is the one-bit padding of `Ext (List.ofFn x)`:
`extBit Ext n x = padFin 1 (Ext (List.ofFn x))`. -/
theorem extBit_eq (Ext : List Bool → List Bool) (n : ℕ) (x : Fin n → Bool) :
    extBit Ext n x = padFin 1 (Ext (List.ofFn x)) := rfl

/-- **Theorem 183.6: no efficient `1`-bit `1/4`-extractor for efficient `(n − 2)`-sources**
[PS10, Theorem 183.6]: for every polynomial-time `Ext` and every `n`, `Ext` is not a
`1/4`-extractor for the efficiently samplable `(n − 2)`-sources on `{0,1}^n`.

**Proof sketch** (the source's, made explicit; fix `n`).
1. `U_n` is the law of the uniform PPT that outputs its coins, and it is an `n`-source, hence an
   `(n − 2)`-source (`isSource_uniform`, `IsSource.mono`). If `Ext` is not `1/4`-close to `U_1` on
   it, `U_n` is the witness.
2. Otherwise `q = Pr[Ext(U_n) = 1] ≥ 1/4`, so `S = {x : Ext(x) = 1}` has `|S| ≥ 2^{n−2}`.
3. The sampler `X` with `11n` coins tries up to 10 `n`-bit blocks for `Ext(x) = 1`, else outputs
   the 11th block. It is a uniform PPT because `Ext` is polynomial-time (`polyTimeComputable_ite`,
   `polyTimeComputable_iterateFind`).
4. Its law is the mixture `(1 − q)^{10} U_n + (1 − (1 − q)^{10}) flat(S)` (rejection sampling).
   Both components are `(n − 2)`-sources, and min-entropy is preserved by mixtures (each point has
   probability at most `2^{−(n−2)}`).
5. `Pr[Ext(X) = 1] = 1 − (1 − q)^{11} ≥ 1 − (3/4)^{11} > 3/4`, so the statistical distance from
   `U_1` exceeds `1/4` (`abs_probTrue_sub_le_statDist`). `X` is the witness. -/
theorem not_isExtractor_effSources (Ext : List Bool → List Bool) (hExt : PolyTimeComputable Ext)
    (n : ℕ) :
    ¬ IsExtractor (effSources (fun n => (n : ℝ) - 2) n) (1 / 4) (extBit Ext n) := by
  sorry

end TCSlib.Cryptography.Randomness
