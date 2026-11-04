/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.FinDist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Entropy, min-entropy and sources

Two measures of how much randomness a distribution on a finite type contains, and the classes of
"imperfect random sources" that extractors are asked to handle.

Shannon entropy is the expected surprise `∑ₓ Pr[X = x] · log₂ (1 / Pr[X = x])`. It is the wrong
measure for extraction from a single sample: a source that is constant with probability `0.99`
and uniform otherwise has Shannon entropy close to `n / 100` on `n`-bit strings, but a
deterministic extractor sees the constant almost always. Min-entropy, `log₂ (1 / maxₓ Pr[X = x])`,
is the right measure: it lower-bounds the surprise of *every* outcome. A `k`-source is a
distribution of min-entropy at least `k`; a `k`-flat source is uniform on `2^k` points.

The library already expresses "min-entropy at least `k`" as the bound
`FinDist.HasMinEntropy p k : ∀ a, p a ≤ 2 ^ (-k)`, which is what the leftover hash lemma consumes.
This file adds the min-entropy *value* that [PS10] defines and proves the two agree
(`FinDist.le_minEntropy_iff`).

## Main definitions

* `FinDist.shannonEntropy`: Shannon entropy in bits.
* `FinDist.maxProb`, `FinDist.minEntropy`: the largest point probability, and min-entropy in bits.
* `FinDist.IsSource k p`: `p` is a `k`-source (min-entropy at least `k`).
* `FinDist.IsFlatSource k p`: `p` is uniform on a set of `2^k` points.
* `FinDist.flat s`: the uniform distribution on a nonempty finite set `s`.

## Main results

* `FinDist.shannonEntropy_uniform`: the uniform distribution on `α` has Shannon entropy
  `log₂ |α|`; on `n`-bit strings, `n` (`FinDist.shannonEntropy_uniform_bits`).
* `FinDist.le_minEntropy_iff`: `k ≤ H∞(p)` exactly when every outcome has probability at most
  `2^(-k)`.
* `FinDist.IsFlatSource.isSource`: a `k`-flat source is a `k`-source.
* `FinDist.isFlatSource_flat`, `FinDist.isSource_uniform`: flat sources and `k`-sources exist.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.3.2 (Definitions 182.3, 183.4 and 183.5).
* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.1.
-/

namespace TCSlib.InformationTheory

open Finset Real

namespace FinDist

variable {α : Type*} [Fintype α]

/-! ### Shannon entropy -/

/-- The **Shannon entropy** of `p` in bits: `H(p) = ∑ₓ p(x) · log₂ (1 / p(x))`, where an outcome of
probability zero contributes zero (`Real.negMulLog 0 = 0`). [PS10, Def 182.3]

**Deviation:** [PS10] defines entropy for a general logarithm and calls the base-2 case Shannon
entropy; only the base-2 case is defined here. -/
noncomputable def shannonEntropy (p : FinDist α) : ℝ :=
  ∑ a, negMulLog (p a) / log 2

/-- Shannon entropy is nonnegative: each term `-p log₂ p` is nonnegative for `0 ≤ p ≤ 1`. -/
theorem shannonEntropy_nonneg (p : FinDist α) : 0 ≤ shannonEntropy p :=
  sum_nonneg fun a _ =>
    div_nonneg (negMulLog_nonneg (p.nonneg a) (p.le_one a)) (log_nonneg one_le_two)

/-- The uniform distribution on `α` has Shannon entropy `log₂ |α|`. [PS10, p. 182, the uniform
example after Def 182.3]

**Proof sketch.** Every one of the `|α|` terms is `(1/|α|) · log₂ |α|`. -/
theorem shannonEntropy_uniform [Nonempty α] :
    shannonEntropy (uniform α) = logb 2 (Fintype.card α) := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [shannonEntropy, uniform_apply, negMulLog, log_inv, sum_const, card_univ,
    nsmul_eq_mul, logb]
  field_simp

/-- The uniform distribution on `n`-bit strings has Shannon entropy `n`. [PS10, p. 182] -/
theorem shannonEntropy_uniform_bits (n : ℕ) :
    shannonEntropy (uniform (Fin n → Bool)) = n := by
  rw [shannonEntropy_uniform]
  simp [Fintype.card_bool, Fintype.card_fin, Real.logb_pow]

/-! ### Min-entropy -/

/-- The largest probability of a single outcome, `maxₓ p(x)`. -/
noncomputable def maxProb (p : FinDist α) : ℝ :=
  univ.sup' (univ_nonempty_iff.2 (Fintype.card_pos_iff.1 p.card_pos)) p

/-- Every outcome's probability is at most the largest one. -/
theorem le_maxProb (p : FinDist α) (a : α) : p a ≤ maxProb p :=
  le_sup' (f := p.prob) (mem_univ a)

/-- The largest probability is at most `c` exactly when every outcome's probability is. -/
theorem maxProb_le_iff (p : FinDist α) {c : ℝ} : maxProb p ≤ c ↔ ∀ a, p a ≤ c := by
  simp [maxProb, sup'_le_iff]

/-- The most likely outcome has positive probability, since the probabilities sum to one. -/
theorem maxProb_pos (p : FinDist α) : 0 < maxProb p := by
  by_contra h
  have hle : ∀ a, p a ≤ 0 := (maxProb_le_iff p).1 (not_lt.1 h)
  have : ∑ a, p a ≤ 0 := sum_nonpos fun a _ => hle a
  rw [p.sum_prob] at this
  norm_num at this

/-- The **min-entropy** of `p` in bits: `H∞(p) = minₓ log₂ (1 / p(x)) = -log₂ (maxₓ p(x))`.
[PS10, Def 183.4] -/
noncomputable def minEntropy (p : FinDist α) : ℝ :=
  -logb 2 (maxProb p)

/-- **Min-entropy in bound form.** `H∞(p) ≥ k` exactly when every outcome has probability at most
`2^(-k)`, which is the library's `HasMinEntropy p k`. This is the "equivalently" of
[PS10, Def 183.4].

**Proof sketch.** `k ≤ -log₂ m ↔ log₂ m ≤ -k ↔ m ≤ 2^(-k)` for the positive maximum `m`, and
`m ≤ c` exactly when every point probability is at most `c`. -/
theorem le_minEntropy_iff (p : FinDist α) (k : ℝ) :
    k ≤ minEntropy p ↔ HasMinEntropy p k := by
  rw [minEntropy, le_neg, logb_le_iff_le_rpow one_lt_two (maxProb_pos p), maxProb_le_iff]
  rfl

/-! ### Sources -/

/-- `p` is a **`k`-source**: its min-entropy is at least `k`. [PS10, Def 183.5] -/
def IsSource (k : ℝ) (p : FinDist α) : Prop :=
  k ≤ minEntropy p

/-- A `k`-source is exactly a distribution with `HasMinEntropy p k`, so the leftover hash lemma
applies to `k`-sources. -/
theorem isSource_iff_hasMinEntropy {k : ℝ} {p : FinDist α} :
    IsSource k p ↔ HasMinEntropy p k :=
  le_minEntropy_iff p k

/-- A `k`-source is a `k'`-source for every `k' ≤ k`. -/
theorem IsSource.mono {k k' : ℝ} {p : FinDist α} (h : IsSource k p) (hk : k' ≤ k) :
    IsSource k' p :=
  hk.trans h

/-- `p` is a **`k`-flat source**: it is the uniform distribution on some set of `2^k` distinct
points. [PS10, Def 183.5]

**Deviation:** [PS10] requires a flat source to be a `k`-source as well; that is automatic
(`IsFlatSource.isSource`), so it is a theorem here rather than part of the definition. -/
def IsFlatSource [DecidableEq α] (k : ℕ) (p : FinDist α) : Prop :=
  ∃ s : Finset α, #s = 2 ^ k ∧ ∀ a, p a = if a ∈ s then ((2 : ℝ) ^ k)⁻¹ else 0

/-- A `k`-flat source is a `k`-source: every point has probability `2^(-k)` or `0`. -/
theorem IsFlatSource.isSource [DecidableEq α] {k : ℕ} {p : FinDist α} (h : IsFlatSource k p) :
    IsSource k p := by
  obtain ⟨s, -, hp⟩ := h
  refine isSource_iff_hasMinEntropy.2 fun a => ?_
  rw [hp a, rpow_neg zero_le_two, rpow_natCast]
  split_ifs
  · exact le_rfl
  · positivity

/-- The uniform distribution on a nonempty finite set `s`. -/
noncomputable def flat [DecidableEq α] (s : Finset α) (hs : s.Nonempty) : FinDist α where
  prob a := if a ∈ s then (#s : ℝ)⁻¹ else 0
  nonneg a := by split_ifs <;> positivity
  sum_prob := by
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
    have : (#s : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hs.card_pos.ne'
    field_simp

/-- The flat distribution gives each point of `s` probability `1 / |s|` and every other point
probability zero. -/
@[simp] theorem flat_apply [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (a : α) :
    flat s hs a = if a ∈ s then (#s : ℝ)⁻¹ else 0 := rfl

/-- The uniform distribution on a set of `2^k` points is a `k`-flat source. -/
theorem isFlatSource_flat [DecidableEq α] {k : ℕ} (s : Finset α) (hs : #s = 2 ^ k) :
    IsFlatSource k (flat s (Finset.card_pos.1 (hs ▸ pow_pos two_pos k))) :=
  ⟨s, hs, fun a => by simp [hs]⟩

/-- The uniform distribution on `α` is a `log₂ |α|`-source; on `n`-bit strings, an `n`-source. -/
theorem isSource_uniform [Nonempty α] : IsSource (logb 2 (Fintype.card α)) (uniform α) := by
  refine isSource_iff_hasMinEntropy.2 fun a => ?_
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [uniform_apply, rpow_neg zero_le_two, rpow_logb two_pos (by norm_num) hc]

end FinDist

end TCSlib.InformationTheory
