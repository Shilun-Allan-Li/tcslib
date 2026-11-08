/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.Entropy
import TCSlib.InformationTheory.LeftoverHash

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Closeness and deterministic extractors

An extractor turns a sample from an imperfect random source into bits that are close to uniform.
"Close" is `ε`-closeness: no distinguisher, however powerful, tells the two distributions apart
with advantage more than `ε`. This file defines closeness in that distinguisher form, proves that
it is the same as a bound on the library's statistical distance `statDist`, defines deterministic
extractors for a class of sources, and restates the leftover hash lemma in extractor terms: a
universal hash family is a *strong* extractor for every class of `k`-sources.

## Main definitions

* `EpsClose ε p q`: `p` and `q` are `ε`-close.
* `IsExtractor C ε Ext`: `Ext` is an `ε`-extractor for the class of sources `C`.
* `IsStrongExtractor C ε f`: the seeded family `f` is a strong `ε`-extractor for `C`: the pair
  (seed, output) is `ε`-close to uniform.
* `seededSources S C`: the sources that carry a uniform seed in `S` beside a sample of a source in
  `C`; the deterministic reading of a seeded extractor.

## Main results

* `abs_probTrue_sub_le_statDist`, `epsClose_iff_statDist_le`: `ε`-closeness is exactly
  `statDist ≤ ε`; the optimal distinguisher accepts the points where the first distribution is
  more likely.
* `isStrongExtractor_of_isUniversal`: **the leftover hash lemma as an extractor** — a universal
  family is a strong `½ √(|β| · 2^(-k))`-extractor for `k`-sources.
* `IsStrongExtractor.isExtractor_seeded`: a strong extractor is a deterministic extractor
  ([PS10, Def 181.2]) for its seeded sources.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.3.1 (Definitions 181.1 and 181.2) and §8.3.3 (the leftover hash lemma, heading only).
* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.1–6.2 (statistical difference,
  strong extractors, Thm 6.18).
* [HILL99] J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A pseudorandom generator from any
  one-way function*, SICOMP 28(4), 1999 (Lemma 4.8).
-/

namespace TCSlib.InformationTheory

open Finset FinDist

variable {α β S : Type*} [Fintype α] [Fintype β] [Fintype S]

/-! ### Closeness -/

/-- `p` and `q` are **`ε`-close**, written `p ≈_ε q`: every deterministic distinguisher `D`, with
no bound on its running time, has advantage at most `ε`,
`|Pr[x ← p : D(x) = 1] - Pr[y ← q : D(y) = 1]| ≤ ε`. [PS10, Def 181.1] -/
def EpsClose (ε : ℝ) (p q : FinDist α) : Prop :=
  ∀ D : α → Bool, |p.probTrue D - q.probTrue D| ≤ ε

/-- The probability differences of two distributions sum to zero. -/
private theorem sum_sub_eq_zero (p q : FinDist α) : ∑ a, (p a - q a) = 0 := by
  rw [sum_sub_distrib, p.sum_prob, q.sum_prob, sub_self]

/-- **No distinguisher beats statistical distance.** For every test `D`,
`|Pr_p[D = 1] - Pr_q[D = 1]| ≤ statDist p q`. [Vad12, §6.1]

**Proof sketch.** Let `d = p - q` and let `A` be the accepted set. Since `d` sums to zero, the sum
of `d` over `A` is minus its sum over the complement, so twice its absolute value is at most
`∑_A |d| + ∑_{Aᶜ} |d| = ∑ |d| = 2 · statDist p q`. -/
theorem abs_probTrue_sub_le_statDist (p q : FinDist α) (D : α → Bool) :
    |p.probTrue D - q.probTrue D| ≤ statDist p q := by
  rw [FinDist.probTrue_sub_probTrue]
  have hsplit := sum_filter_add_sum_filter_not univ (fun a => D a = true) (fun a => p a - q a)
  have hsplitabs :=
    sum_filter_add_sum_filter_not univ (fun a => D a = true) (fun a => |p a - q a|)
  rw [sum_sub_eq_zero] at hsplit
  have h1 := abs_sum_le_sum_abs (fun a => p a - q a) (univ.filter (fun a => D a = true))
  have h2 := abs_sum_le_sum_abs (fun a => p a - q a) (univ.filter (fun a => ¬ D a = true))
  have hc : ∑ a ∈ univ.filter (fun a => ¬ D a = true), (p a - q a)
      = -∑ a ∈ univ.filter (fun a => D a = true), (p a - q a) := by linarith
  rw [hc, abs_neg] at h2
  have hd : statDist p q = (1 / 2) * ∑ a, |p a - q a| := rfl
  linarith

/-- **The optimal distinguisher attains statistical distance.** If every test has advantage at
most `ε`, then `statDist p q ≤ ε`. [Vad12, §6.1]

**Proof sketch.** Test `D` accepting exactly the points where `p` is more likely than `q`. On the
accepted set `|p - q| = p - q`, off it `|p - q| = q - p`, and the two sums of `p - q` cancel, so
`∑ |p - q|` is twice `D`'s advantage. Hence `statDist p q` equals that advantage, which is at most
`ε`. -/
theorem statDist_le_of_epsClose {ε : ℝ} {p q : FinDist α} (h : EpsClose ε p q) :
    statDist p q ≤ ε := by
  have key := h (fun a => decide (q a < p a))
  rw [FinDist.probTrue_sub_probTrue] at key
  have hpos : ∀ a ∈ univ.filter (fun a => decide (q a < p a) = true),
      |p a - q a| = p a - q a := fun a ha => by
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq] at ha
    exact abs_of_pos (by linarith)
  have hneg : ∀ a ∈ univ.filter (fun a => ¬ decide (q a < p a) = true),
      |p a - q a| = -(p a - q a) := fun a ha => by
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq, not_lt] at ha
    exact abs_of_nonpos (by linarith)
  have hsplit :=
    sum_filter_add_sum_filter_not univ (fun a => decide (q a < p a) = true) (fun a => p a - q a)
  have hsplitabs :=
    sum_filter_add_sum_filter_not univ (fun a => decide (q a < p a) = true) (fun a => |p a - q a|)
  rw [sum_congr rfl hpos, sum_congr rfl hneg, sum_neg_distrib] at hsplitabs
  rw [sum_sub_eq_zero] at hsplit
  have hnn : 0 ≤ ∑ a ∈ univ.filter (fun a => decide (q a < p a) = true), (p a - q a) :=
    sum_nonneg fun a ha => by
      simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq] at ha
      linarith
  rw [abs_of_nonneg hnn] at key
  have hd : statDist p q = (1 / 2) * ∑ a, |p a - q a| := rfl
  linarith

/-- **`ε`-closeness is a statistical-distance bound.** `p ≈_ε q` in the distinguisher form of
[PS10, Def 181.1] exactly when `statDist p q ≤ ε`. [Vad12, §6.1] -/
theorem epsClose_iff_statDist_le {ε : ℝ} {p q : FinDist α} :
    EpsClose ε p q ↔ statDist p q ≤ ε :=
  ⟨statDist_le_of_epsClose, fun h D => (abs_probTrue_sub_le_statDist p q D).trans h⟩

/-- Closeness is symmetric. An elementary consequence of [PS10, Def 181.1]. -/
theorem EpsClose.symm {ε : ℝ} {p q : FinDist α} (h : EpsClose ε p q) : EpsClose ε q p := by
  rw [epsClose_iff_statDist_le] at h ⊢
  rwa [statDist_comm]

/-- Closeness composes: `p ≈_ε q` and `q ≈_δ r` give `p ≈_{ε+δ} r`. An elementary consequence of
[PS10, Def 181.1]. -/
theorem EpsClose.trans {ε δ : ℝ} {p q r : FinDist α} (h₁ : EpsClose ε p q)
    (h₂ : EpsClose δ q r) : EpsClose (ε + δ) p r := by
  rw [epsClose_iff_statDist_le] at *
  exact (statDist_triangle p q r).trans (add_le_add h₁ h₂)

/-! ### Extractors -/

/-- `Ext` is an **`ε`-extractor for the class of sources `C`**: a deterministic function whose
output on a sample of any source in `C` is `ε`-close to uniform, `Ext(X) ≈_ε U`.
[PS10, Def 181.2]

**Deviation:** [PS10] takes `Ext : {0,1}^n → {0,1}^m`; here the domain and range are any finite
types, the source's case being `α = Fin n → Bool` and `β = Fin m → Bool`. -/
def IsExtractor [DecidableEq β] [Nonempty β] (C : Set (FinDist α)) (ε : ℝ) (Ext : α → β) :
    Prop :=
  ∀ X ∈ C, EpsClose ε (X.map Ext) (uniform β)

/-- `Ext` is an `ε`-extractor for `C` exactly when `Ext(X)` is `ε`-close to uniform for every
`X ∈ C`. -/
theorem isExtractor_iff [DecidableEq β] [Nonempty β] {C : Set (FinDist α)} {ε : ℝ}
    {Ext : α → β} : IsExtractor C ε Ext ↔ ∀ X ∈ C, EpsClose ε (X.map Ext) (uniform β) :=
  Iff.rfl

/-- An extractor for a class is one for every subclass. -/
theorem IsExtractor.mono [DecidableEq β] [Nonempty β] {C C' : Set (FinDist α)} {ε : ℝ}
    {Ext : α → β} (h : IsExtractor C ε Ext) (hC : C' ⊆ C) : IsExtractor C' ε Ext :=
  fun X hX => h X (hC hX)

/-- The seeded family `f : S → α → β` is a **strong `ε`-extractor for `C`**: for every source `X`
in `C`, the pair `(s, f s x)` with a uniform seed `s` and `x ← X` is `ε`-close to uniform on
`S × β`. [Vad12, Ch. 6, strong extractors]. [PS10] has no such definition: its §8.3.3 (the
leftover hash lemma) contains only a heading.

**Deviation:** [Vad12] defines strong `(k, ε)`-extractors on bit strings, for the class of
`k`-sources; here the class `C` and the finite seed, input and output types are arbitrary. -/
def IsStrongExtractor [DecidableEq S] [DecidableEq α] [DecidableEq β] [Nonempty S] [Nonempty β]
    (C : Set (FinDist α)) (ε : ℝ) (f : S → α → β) : Prop :=
  ∀ X ∈ C, EpsClose ε (hashPair f X) (uniform (S × β))

/-- `f` is a strong `ε`-extractor for `C` exactly when `(s, f s x)` is `ε`-close to uniform on
`S × β` for every `X ∈ C`. -/
theorem isStrongExtractor_iff [DecidableEq S] [DecidableEq α] [DecidableEq β] [Nonempty S]
    [Nonempty β] {C : Set (FinDist α)} {ε : ℝ} {f : S → α → β} :
    IsStrongExtractor C ε f ↔ ∀ X ∈ C, EpsClose ε (hashPair f X) (uniform (S × β)) :=
  Iff.rfl

/-- The **seeded sources** over `C`: a uniform seed in `S` paired with an independent sample of a
source in `C`. A strong extractor is a deterministic extractor ([PS10, Def 181.2]) for exactly
these. -/
def seededSources [Nonempty S] (C : Set (FinDist α)) : Set (FinDist (S × α)) :=
  {Y | ∃ X ∈ C, Y = FinDist.prod (uniform S) X}

/-- The seeded sources over `C` are exactly the products of the uniform seed with a source in
`C`. -/
theorem mem_seededSources [Nonempty S] {C : Set (FinDist α)} {Y : FinDist (S × α)} :
    Y ∈ seededSources (S := S) C ↔ ∃ X ∈ C, Y = FinDist.prod (uniform S) X :=
  Iff.rfl

/-- A strong extractor `f` makes `(s, x) ↦ (s, f s x)` a deterministic `ε`-extractor
([PS10, Def 181.2]) for the seeded sources over `C`: the seed is part of the sample and is
output again. -/
theorem IsStrongExtractor.isExtractor_seeded [DecidableEq S] [DecidableEq α] [DecidableEq β]
    [Nonempty S] [Nonempty β] {C : Set (FinDist α)} {ε : ℝ} {f : S → α → β}
    (h : IsStrongExtractor C ε f) :
    IsExtractor (seededSources (S := S) C) ε (fun p : S × α => (p.1, f p.1 p.2)) := by
  rintro Y ⟨X, hX, rfl⟩
  exact h X hX

/-- **The leftover hash lemma as an extractor.** A universal hash family `f : S → α → β` is a
strong `½ √(|β| · 2^(-k))`-extractor for the `k`-sources on `α`. [HILL99, Lemma 4.8],
[Vad12, Thm 6.18]; [PS10, §8.3.3] carries this title but no text.

**Deviation:** stated over arbitrary finite types, for min-entropy `k` and for `f` universal in
the collision-count sense of `IsUniversal`, with the error in closed form (for `|β| = 2^m` it is
`2^((m - k)/2 - 1)`); the cited statements are over bit strings and are not phrased in exactly
these terms.

**Proof sketch.** A `k`-source has `HasMinEntropy X k` (`isSource_iff_hasMinEntropy`), so the
library's `leftover_hash` bounds the statistical distance of `(s, f s x)` from uniform by
`½ √(|β| · 2^(-k))`, and statistical distance bounds every distinguisher's advantage
(`epsClose_iff_statDist_le`). -/
theorem isStrongExtractor_of_isUniversal [DecidableEq S] [DecidableEq α] [DecidableEq β]
    [Nonempty S] [Nonempty β] {f : S → α → β} (hf : IsUniversal f) (k : ℝ) :
    IsStrongExtractor {X : FinDist α | IsSource k X}
      ((1 / 2) * Real.sqrt (Fintype.card β * (2 : ℝ) ^ (-k))) f :=
  fun _ hX => epsClose_iff_statDist_le.2 (leftover_hash hf (isSource_iff_hasMinEntropy.1 hX))

end TCSlib.InformationTheory
