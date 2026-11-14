/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.Entropy
import TCSlib.InformationTheory.Extractors
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Randomness.Extraction.Rejection
import TCSlib.Cryptography.Randomness.Extraction.Sampler

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

## Contents

* `Randomness.Extraction.Rejection`: finite rejection laws and source-preserving mixtures.
* `Randomness.Extraction.Sampler`: the uniform machine and its consecutive coin blocks.

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

/-- The uniform sampler at the fixed width `n` outputs its `n` coin bits and has no advice. -/
noncomputable def uniformSampler (n : ℕ) : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD (.const n)

/-- The uniform sampler uses the constant coin polynomial `n`. -/
theorem uniformSampler_coins (n : ℕ) : (uniformSampler n).coins = .const n :=
  NUPPT.coins_ofPolyTimeUniform polyTimeComputable_pairSndD (.const n)

/-- The uniform sampler has empty advice at every activation parameter. -/
theorem uniformSampler_uniform (n : ℕ) : (uniformSampler n).Uniform :=
  NUPPT.ofPolyTimeUniform_uniform polyTimeComputable_pairSndD (.const n)

/-- The uniform sampler returns the encoding of its coin vector. -/
theorem uniformSampler_runAt (n : ℕ) (r : (uniformSampler n).Coins n) :
    (uniformSampler n).runAt n [] r = List.ofFn r := by
  rw [NUPPT.runAt_eq]
  change (NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD (.const n)).runAtL
    n [] (List.ofFn r) = _
  rw [NUPPT.runAtL_ofPolyTimeUniform, pairSndD_pairEncode]

/-- The coins of the uniform sampler are canonically the `n`-bit vectors. -/
noncomputable def uniformSamplerCoins (n : ℕ) :
    (uniformSampler n).Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsEquivPoly (uniformSampler_coins n) n).trans
    (Equiv.arrowCongr (finCongr (PolyExpr.eval_const n n)) (Equiv.refl Bool))

/-- The canonical uniform-sampler coin equivalence is the composition of the published
coin-polynomial identification with the constant-polynomial width equality. -/
theorem uniformSamplerCoins_eq (n : ℕ) : uniformSamplerCoins n =
    (NUPPT.coinsEquivPoly (uniformSampler_coins n) n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_const n n)) (Equiv.refl Bool)) := rfl

/-- The uniform sampler's coin equivalence preserves the encoded word. -/
theorem uniformSamplerCoins_ofFn (n : ℕ) (r : (uniformSampler n).Coins n) :
    List.ofFn (uniformSamplerCoins n r) = List.ofFn r := by
  rw [uniformSamplerCoins, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquivPoly_ofFn]

/-- The law of the sampler that returns its coins is the uniform law on `n`-bit strings.
The coin equivalence preserves encodings, and a bijection preserves uniformity. -/
theorem samplerLaw_uniformSampler (n : ℕ) :
    samplerLaw (uniformSampler n) n = FinDist.uniform (Fin n → Bool) := by
  have hread : (fun r : (uniformSampler n).Coins n =>
      padFin n ((uniformSampler n).runAt n [] r)) = uniformSamplerCoins n := by
    funext r
    rw [uniformSampler_runAt, ← uniformSamplerCoins_ofFn n r, padFin_ofFn]
  rw [samplerLaw, hread]
  exact Rejection.map_uniform_equiv (uniformSamplerCoins n)

/-- Uniform `n`-bit strings form an efficiently samplable `(n−2)`-source. -/
theorem uniform_mem_effSources (n : ℕ) :
    FinDist.uniform (Fin n → Bool) ∈ effSources (fun n => (n : ℝ) - 2) n := by
  have hu : FinDist.IsSource (n : ℝ) (FinDist.uniform (Fin n → Bool)) := by
    simpa [Fintype.card_bool, Fintype.card_fin, Real.logb_pow] using
      (FinDist.isSource_uniform (α := Fin n → Bool))
  exact (effSources_iff _ _ _).2
    ⟨uniformSampler n, uniformSampler_uniform n, (samplerLaw_uniformSampler n).symm,
      hu.mono (by linarith)⟩

/-- The first output bit read by `extBit` is the head of the extractor's output,
with `false` for an empty output. -/
theorem extBit_zero (Ext : List Bool → List Bool) (n : ℕ) (x : Fin n → Bool) :
    extBit Ext n x 0 = (Ext (List.ofFn x)).headD false := by
  rw [extBit_eq, padFin_apply]
  cases Ext (List.ofFn x) <;> rfl

/-- A uniform one-bit word has its first bit true with probability `1/2`. -/
theorem uniform_one_probTrue :
    (FinDist.uniform (Fin 1 → Bool)).probTrue (fun x => x 0) = 1 / 2 := by
  classical
  rw [FinDist.probTrue_eq]
  have hs : (Finset.univ : Finset (Fin 1 → Bool)).filter (fun x => x 0 = true) =
      {fun _ => true} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using h
    · rintro rfl
      rfl
  rw [hs, Finset.sum_singleton, FinDist.uniform_apply]
  norm_num

/-- If the candidate extractor succeeds on every efficient `(n−2)`-source, then its first
bit on the uniform source is true with probability at least `1/4`.
The uniform source is efficient, so its output is within `1/4` of a fair bit. -/
theorem uniform_acceptance_lower (Ext : List Bool → List Bool) (n : ℕ)
    (h : IsExtractor (effSources (fun n => (n : ℝ) - 2) n) (1 / 4) (extBit Ext n)) :
    1 / 4 ≤ (FinDist.uniform (Fin n → Bool)).probTrue (fun x => extBit Ext n x 0) := by
  have hclose := (isExtractor_iff.1 h) _ (uniform_mem_effSources n)
  have hb := (abs_probTrue_sub_le_statDist
    ((FinDist.uniform (Fin n → Bool)).map (extBit Ext n))
    (FinDist.uniform (Fin 1 → Bool)) (fun x => x 0)).trans
      (epsClose_iff_statDist_le.1 hclose)
  rw [Rejection.probTrue_map, uniform_one_probTrue] at hb
  have hl := (abs_le.1 hb).1
  linarith

/-- The bounded rejection machine's law at width `n` is the finite first-success law
on `t` trials and an independent uniform fallback.

**Proof sketch.** Its coin equivalence followed by the canonical block equivalence is a
bijection onto independent uniform blocks. The machine reader identifies its output with
the typed selector, whose pushforward is the rejection law. -/
theorem samplerLaw_rejection {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t : ℕ) :
    samplerLaw (RejectionSampler.machine hExt n t) n =
      Rejection.law (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) t := by
  let D := fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false
  let e := (RejectionSampler.coinEquiv hExt n t n).trans (FunFamily.blocks (t + 1) n)
  have hread : (fun r : (RejectionSampler.machine hExt n t).Coins n =>
      padFin n ((RejectionSampler.machine hExt n t).runAt n [] r)) =
      (fun r => Rejection.select D t (e r)) := by
    funext r
    rw [RejectionSampler.machine_runAt, ← RejectionSampler.coinEquiv_ofFn hExt n t n r,
      RejectionSampler.chooseWord_blocks, padFin_ofFn]
    rfl
  rw [samplerLaw, hread,
    ← Rejection.map_map (FinDist.uniform ((RejectionSampler.machine hExt n t).Coins n))
      e (Rejection.select D t), Rejection.map_uniform_equiv e]
  exact Rejection.select_uniform_law D t

/-- Dividing a uniform `n`-bit point mass by `1/4` gives the exact `(n−2)`-source bound,
including `n=0,1,2`: `4 / 2^n = 2^(-(n-2))`. -/
theorem uniform_card_div_quarter (n : ℕ) :
    (Fintype.card (Fin n → Bool) : ℝ)⁻¹ / (1 / 4) =
      (2 : ℝ) ^ (-((n : ℝ) - 2)) := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [show -((n : ℝ) - 2) = 2 - (n : ℝ) by ring,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  norm_num
  ring

/-- When uniform acceptance is at least `1/4`, ten rejection trials and a fresh fallback
produce an efficiently samplable `(n−2)`-source.

**Proof sketch.** The accepted flat source has point mass at most `1/(2^n q) ≤ 4/2^n`,
so it and the uniform law are `(n−2)`-sources. The exact convex mixture identity preserves
that bound, and the uniform machine realizes the mixture with `11n` coins. -/
theorem rejection_mem_effSources {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n : ℕ)
    (hq : 1 / 4 ≤ (FinDist.uniform (Fin n → Bool)).probTrue
      (fun a => (Ext (List.ofFn a)).headD false)) :
    Rejection.law (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) 10 ∈
      effSources (fun n => (n : ℝ) - 2) n := by
  let D := fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false
  have hqpos : 0 < (FinDist.uniform (Fin n → Bool)).probTrue D := by
    dsimp only [D]
    linarith
  have hbound : (Fintype.card (Fin n → Bool) : ℝ)⁻¹ /
      (FinDist.uniform (Fin n → Bool)).probTrue D ≤ (2 : ℝ) ^ (-((n : ℝ) - 2)) := by
    calc _ ≤ (Fintype.card (Fin n → Bool) : ℝ)⁻¹ / (1 / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hq
      _ = _ := uniform_card_div_quarter n
  obtain ⟨_, _, _, hU⟩ := (effSources_iff _ _ _).1 (uniform_mem_effSources n)
  have hflat := Rejection.accepted_flat_isSource D (Rejection.accepted_nonempty D hqpos)
    ((n : ℝ) - 2) hbound
  exact (effSources_iff _ _ _).2
    ⟨RejectionSampler.machine hExt n 10, RejectionSampler.machine_uniform hExt n 10,
      (samplerLaw_rejection hExt n 10).symm,
      Rejection.law_isSource D hqpos 10 ((n : ℝ) - 2) hU hflat⟩

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
  intro h
  have hq := uniform_acceptance_lower Ext n h
  sorry

end TCSlib.Cryptography.Randomness
