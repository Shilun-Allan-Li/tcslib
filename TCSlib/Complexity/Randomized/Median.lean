/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.List.Sort

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finding the median: `FindKthElement` and Claim 7.4

The randomized selection algorithm of [AB09, §7.2.1]: pick a uniformly random pivot of the
current list, count the elements below it, and either output it or recurse on one side.
A run is a `PMF` (Mathlib's probability mass functions) over pairs
(output, number of comparisons); the pivot is `PMF.uniformOfFintype` over the list's indices.

## Main definitions

* `Randomized.IsKthSmallest`, `Randomized.IsMedian` — the k-th smallest element and a median.
* `Randomized.findKthElement` — Algorithm FindKthElement as a distribution over runs.
* `Randomized.expectedComparisons`, `Randomized.maxExpectedComparisons` — `T(k, a)`, `T(n)`.

## Main results

* `Randomized.findKthElement_correct` — every possible output is the k-th smallest;
  `Randomized.findKthElement_isMedian` for `k = ⌈n/2⌉`.
* `Randomized.findKthElement_comparisons_le` — every run halts after ≤ n(n+1)/2 comparisons.
* `Randomized.maxExpectedComparisons_le` — Claim 7.4: `T(n) ≤ 10 n`.

## Divergences

* **What is counted.** The cost of a call on a list of length `n` is `n` comparisons (the scan
  of step 2, each comparison three-way; the partition reuses its outcomes). This is the book's
  `cn` with `c = 1`, so Claim 7.4 is proved as `T(n) ≤ 10 n`, exactly the book's inequality.
* **Strict partition.** Step 4 recurses on `{aᵢ < x}`, not the printed `{aᵢ ≤ x}`. As printed,
  if `x` is the maximum and `k < n` the recursive call is on the same list, so the algorithm
  need not terminate (on `[a, a]` with `k = 1` every pivot recurses on `[a, a]` again) and the
  book's induction would use `T(n)` to bound `T(n)`; with `<` the
  list shrinks and the j-th pivot costs `T(j - 1) ≤ T(j)`, so the book's sum still bounds it.
* **Multisets.** The test "`m = k`" becomes "`#{aᵢ < x} < k ≤ m`", which on distinct elements
  is exactly `m = k` (`isKthSmallest_iff_of_nodup`); this makes the algorithm correct on lists
  with repetitions as well, with the k-th smallest counted with multiplicity.
* **Proof of Claim 7.4.** The book splits on `k` and uses `∑_{j<k} j ≥ k²/2.5` "for large
  enough `k`"; we bound the recursive list for the j-th smallest pivot by
  `max (j - 1) (n - j)` for every `k`, and `∑_j max (j - 1) (n - j) ≤ 3n²/4 ≤ 9n²/10`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open scoped ENNReal

variable {α : Type*} [LinearOrder α]

/-! ### The k-th smallest element and medians -/

/-- `y` is a `k`-th smallest element of `l` (with multiplicity): `y` occurs in `l`, fewer than
`k` entries are `< y` and at least `k` entries are `≤ y`. [AB09, §7.2.1] -/
def IsKthSmallest (l : List α) (k : ℕ) (y : α) : Prop :=
  y ∈ l ∧ l.countP (· < y) < k ∧ k ≤ l.countP (· ≤ y)

/-- `x` is a median of `a₁, …, aₙ`: at least `n/2` of the `aᵢ` are `≤ x` and at least `n/2`
are `≥ x`. [AB09, §7.2.1] -/
def IsMedian (l : List α) (x : α) : Prop :=
  l.length ≤ 2 * l.countP (· ≤ x) ∧ l.length ≤ 2 * l.countP (x ≤ ·)

/-- Every entry is either `> x` or `≤ x`. -/
private lemma countP_lt_add_countP_le (l : List α) (x : α) :
    l.countP (x < ·) + l.countP (· ≤ x) = l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons, List.length_cons]
    by_cases h : x < a
    · simp [h, not_le.2 h]; omega
    · simp [h, not_lt.1 h]; omega

/-- Every entry is either `< x` or `≥ x`. -/
private lemma countP_lt_add_countP_ge (l : List α) (x : α) :
    l.countP (· < x) + l.countP (x ≤ ·) = l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons, List.length_cons]
    by_cases h : a < x
    · simp [h, not_le.2 h]; omega
    · simp [h, not_lt.1 h]; omega

/-- The entries `≤ y` are those `< y` together with the copies of `y`. -/
private lemma countP_le_eq_countP_lt_add_count (l : List α) (y : α) :
    l.countP (· ≤ y) = l.countP (· < y) + l.count y := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons, List.count_cons]
    rcases lt_trichotomy a y with h | rfl | h
    · simp [h, h.le, h.ne]; omega
    · simp; omega
    · simp [not_le.2 h, not_lt.2 h.le, h.ne']; omega

/-- On a list of distinct elements, `y` is the `k`-th smallest exactly when `y` occurs and
exactly `k` entries are `≤ y` (the book's test `m = k`). [AB09, §7.2.1] -/
theorem isKthSmallest_iff_of_nodup {l : List α} (hl : l.Nodup) {k : ℕ} {y : α} :
    IsKthSmallest l k y ↔ y ∈ l ∧ l.countP (· ≤ y) = k := by
  constructor
  · rintro ⟨hy, h1, h2⟩
    have := countP_le_eq_countP_lt_add_count l y
    rw [List.count_eq_one_of_mem hl hy] at this
    exact ⟨hy, by omega⟩
  · rintro ⟨hy, h⟩
    have := countP_le_eq_countP_lt_add_count l y
    rw [List.count_eq_one_of_mem hl hy] at this
    exact ⟨hy, by omega, by omega⟩

/-- The `k`-th smallest element is unique. -/
theorem IsKthSmallest.unique {l : List α} {k : ℕ} {y z : α} (hy : IsKthSmallest l k y)
    (hz : IsKthSmallest l k z) : y = z := by
  have key : ∀ {y z : α}, IsKthSmallest l k y → IsKthSmallest l k z → ¬ y < z := by
    intro y z hy hz hyz
    have : l.countP (· ≤ y) ≤ l.countP (· < z) :=
      List.countP_mono_left fun a _ h => by simpa using lt_of_le_of_lt (by simpa using h) hyz
    have := hy.2.2; have := hz.2.1; omega
  rcases lt_trichotomy y z with h | h | h
  · exact absurd h (key hy hz)
  · exact h
  · exact absurd h (key hz hy)

/-- Above a pivot `x < y`: the entries `< y` are those above `x` and below `y`, plus all
entries `≤ x`. -/
private lemma countP_lt_eq_countP_filter_add (l : List α) {x y : α} (hxy : x < y) :
    l.countP (· < y) = (l.filter (x < ·)).countP (· < y) + l.countP (· ≤ x) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases hxa : x < a
    · simp [List.countP_cons, hxa, not_le.2 hxa]
      split_ifs <;> omega
    · have : a < y := lt_of_le_of_lt (not_lt.1 hxa) hxy
      simp [hxa, not_lt.1 hxa, this]
      omega

/-- The `≤ y` analogue of `countP_lt_eq_countP_filter_add`. -/
private lemma countP_le_eq_countP_filter_add (l : List α) {x y : α} (hxy : x < y) :
    l.countP (· ≤ y) = (l.filter (x < ·)).countP (· ≤ y) + l.countP (· ≤ x) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases hxa : x < a
    · simp [List.countP_cons, hxa, not_le.2 hxa]
      split_ifs <;> omega
    · have : a ≤ y := (not_lt.1 hxa).trans hxy.le
      simp [hxa, not_lt.1 hxa, this]
      omega

/-- In a sorted list, at most `j` entries are strictly below the `j`-th entry. -/
private lemma countP_lt_getElem_le {s : List α} (hs : s.Pairwise (· ≤ ·)) {j : ℕ}
    (hj : j < s.length) : s.countP (· < s[j]) ≤ j := by
  have hsplit : s.countP (· < s[j]) = (s.take j).countP (· < s[j]) +
      (s.drop j).countP (· < s[j]) := by
    rw [← List.countP_append, List.take_append_drop]
  rw [hsplit]
  have hdrop : (s.drop j).countP (· < s[j]) = 0 := by
    rw [List.countP_eq_zero]
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ha
    rw [List.getElem_drop]
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp
    · have := List.pairwise_iff_getElem.1 hs j (j + t) hj (by simp at ht; omega) (by omega)
      simpa using this
  have := List.countP_le_length (p := (· < s[j])) (l := s.take j)
  rw [hdrop]; simp at this ⊢; omega

/-- In a sorted list of length `n`, at most `n - 1 - j` entries are strictly above the
`j`-th entry. -/
private lemma countP_getElem_lt_le {s : List α} (hs : s.Pairwise (· ≤ ·)) {j : ℕ}
    (hj : j < s.length) : s.countP (s[j] < ·) ≤ s.length - 1 - j := by
  have hsplit : s.countP (s[j] < ·) = (s.take (j + 1)).countP (s[j] < ·) +
      (s.drop (j + 1)).countP (s[j] < ·) := by
    rw [← List.countP_append, List.take_append_drop]
  rw [hsplit]
  have htake : (s.take (j + 1)).countP (s[j] < ·) = 0 := by
    rw [List.countP_eq_zero]
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ha
    rw [List.getElem_take]
    simp only [List.length_take] at ht
    rcases Nat.lt_or_ge t j with htj | htj
    · have := List.pairwise_iff_getElem.1 hs t j (by omega) hj htj
      simpa using this
    · have : t = j := by omega
      subst this; simp
  have := List.countP_le_length (p := (s[j] < ·)) (l := s.drop (j + 1))
  rw [htake]; simp at this ⊢; omega

/-- In a sorted permutation `s` of `l`, the entry at position `k - 1` is the `k`-th smallest
element of `l`. -/
private lemma isKthSmallest_of_sorted {l s : List α} (hp : s.Perm l) (hs : s.Pairwise (· ≤ ·))
    {k : ℕ} (hk : 1 ≤ k) (hj : k - 1 < s.length) : IsKthSmallest l k s[k - 1] := by
  refine ⟨hp.subset (List.getElem_mem hj), ?_, ?_⟩
  · rw [← hp.countP_eq]; have := countP_lt_getElem_le hs hj; omega
  · rw [← hp.countP_eq]
    have := countP_getElem_lt_le hs hj
    have := countP_lt_add_countP_le s s[k - 1]
    omega

/-- The entry at position `k - 1` of the sorted list is the `k`-th smallest; in particular a
`k`-th smallest element exists for `1 ≤ k ≤ n`. -/
theorem isKthSmallest_insertionSort {l : List α} {k : ℕ} (hk : 1 ≤ k)
    (hkl : k ≤ l.length) :
    IsKthSmallest l k ((l.insertionSort (· ≤ ·))[k - 1]'(by
      rw [List.length_insertionSort]; omega)) :=
  isKthSmallest_of_sorted (List.perm_insertionSort _ l) (List.sorted_insertionSort _ l) hk _

/-- The `⌈n/2⌉`-th smallest element is a median. [AB09, §7.2.1] -/
theorem IsKthSmallest.isMedian {l : List α} {y : α}
    (hy : IsKthSmallest l ((l.length + 1) / 2) y) : IsMedian l y := by
  have := countP_lt_add_countP_ge l y
  exact ⟨by have := hy.2.2; omega, by have := hy.2.1; omega⟩

/-! ### The algorithm -/

/-- Algorithm FindKthElement(k, a₁, …, aₙ) of [AB09, §7.2.1] as a distribution over runs
(output, number of comparisons): a uniform pivot `x = aᵢ`, then recurse on `{aⱼ < x}` or on
`{aⱼ > x}` (with `k - #{aⱼ ≤ x}`), or output `x`; a call costs `n` comparisons. -/
noncomputable def findKthElement (k : ℕ) (l : List α) : PMF (Option α × ℕ) :=
  if h : l = [] then PMF.pure (none, 0) else
  haveI : Nonempty (Fin l.length) := ⟨⟨0, List.length_pos_iff.2 h⟩⟩
  (PMF.uniformOfFintype (Fin l.length)).bind fun i =>
    if k ≤ l.countP (· < l[i]) then
      (findKthElement k (l.filter (· < l[i]))).map fun r => (r.1, r.2 + l.length)
    else if l.countP (· ≤ l[i]) < k then
      (findKthElement (k - l.countP (· ≤ l[i])) (l.filter (l[i] < ·))).map
        fun r => (r.1, r.2 + l.length)
    else PMF.pure (some l[i], l.length)
termination_by l.length
decreasing_by
  all_goals
    simp only [List.length_unattach]
    exact lt_of_lt_of_eq (List.length_filter_lt_length_iff_exists.2
      ⟨⟨l[i], List.getElem_mem _⟩, List.mem_attach _ _, by simp⟩) List.length_attach

/-- Every output of FindKthElement(k, a₁, …, aₙ) with `1 ≤ k ≤ n` is the `k`-th smallest
element. [AB09, §7.2.1]

**Proof sketch.** Induction on `n`. The pivot `x` occurs in the list. If `k ≤ #{aⱼ < x}`,
the `k`-th smallest of `{aⱼ < x}` lies below `x`, and every entry below it lies below `x`, so
it is the `k`-th smallest overall; if `m < k`, the `(k - m)`-th smallest `y` of `{aⱼ > x}`
has the `m` entries `≤ x` below it in addition; otherwise `x` itself satisfies the
definition. -/
theorem findKthElement_correct {k : ℕ} {l : List α} (hk : 1 ≤ k) (hkl : k ≤ l.length)
    {r : Option α × ℕ} (hr : r ∈ (findKthElement k l).support) :
    ∃ y, r.1 = some y ∧ IsKthSmallest l k y := by
  rw [findKthElement] at hr
  split_ifs at hr with h
  · subst h; simp at hkl; omega
  rw [PMF.mem_support_bind_iff] at hr
  obtain ⟨i, -, hi⟩ := hr
  set x := l[i]
  split_ifs at hi with h1 h2
  · -- recurse below the pivot
    rw [PMF.support_map] at hi
    obtain ⟨r', hr', rfl⟩ := hi
    have hlen : k ≤ (l.filter (· < x)).length := by rwa [← List.countP_eq_length_filter]
    obtain ⟨y, hy, hy1, hy2, hy3⟩ := findKthElement_correct hk hlen hr'
    have hyx : y < x := by simpa using (List.mem_filter.1 hy1).2
    refine ⟨y, hy, (List.mem_filter.1 hy1).1, ?_, ?_⟩
    · rwa [List.countP_filter, List.countP_congr (q := (· < y))] at hy2
      intro a _; simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, h.trans hyx⟩⟩
    · rwa [List.countP_filter, List.countP_congr (q := (· ≤ y))] at hy3
      intro a _; simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, lt_of_le_of_lt h hyx⟩⟩
  · -- recurse above the pivot
    rw [PMF.support_map] at hi
    obtain ⟨r', hr', rfl⟩ := hi
    have hsplit := countP_lt_add_countP_le l x
    have hlen : k - l.countP (· ≤ x) ≤ (l.filter (x < ·)).length := by
      rw [← List.countP_eq_length_filter]; omega
    obtain ⟨y, hy, hy1, hy2, hy3⟩ := findKthElement_correct (by omega) hlen hr'
    have hxy : x < y := by simpa using (List.mem_filter.1 hy1).2
    have hlt := countP_lt_eq_countP_filter_add l hxy
    have hle := countP_le_eq_countP_filter_add l hxy
    exact ⟨y, hy, (List.mem_filter.1 hy1).1, by omega, by omega⟩
  · -- output the pivot
    rw [PMF.mem_support_pure_iff] at hi
    subst hi
    exact ⟨x, rfl, List.getElem_mem _, by omega, by omega⟩
termination_by l.length
decreasing_by
  all_goals
    exact List.length_filter_lt_length_iff_exists.2 ⟨l[i], List.getElem_mem _, by simp⟩

/-- On a nonempty list, every output of FindKthElement(⌈n/2⌉, a₁, …, aₙ) is a median.
[AB09, §7.2.1] -/
theorem findKthElement_isMedian {l : List α} (hl : l ≠ [])
    {r : Option α × ℕ} (hr : r ∈ (findKthElement ((l.length + 1) / 2) l).support) :
    ∃ y, r.1 = some y ∧ IsMedian l y := by
  have := List.length_pos_iff.2 hl
  obtain ⟨y, hy, hk⟩ := findKthElement_correct (by omega) (by omega) hr
  exact ⟨y, hy, hk.isMedian⟩

/-- Every run of FindKthElement on a list of length `n` halts after at most `n(n+1)/2`
comparisons, whatever the pivots.

**Proof sketch.** Induction on `n`: a call costs `n`, and a recursive call is on a list of
length at most `n - 1` (the pivot is excluded), so the total is at most
`n + (n - 1)n/2 = n(n+1)/2`. -/
theorem findKthElement_comparisons_le {k : ℕ} {l : List α} {r : Option α × ℕ}
    (hr : r ∈ (findKthElement k l).support) : 2 * r.2 ≤ l.length * (l.length + 1) := by
  rw [findKthElement] at hr
  split_ifs at hr with h
  · rw [PMF.mem_support_pure_iff] at hr; subst hr; simp
  rw [PMF.mem_support_bind_iff] at hr
  obtain ⟨i, -, hi⟩ := hr
  have hshort : ∀ p : α → Bool, ¬ p l[i] →
      (l.filter p).length + 1 ≤ l.length := fun p hp =>
    List.length_filter_lt_length_iff_exists.2 ⟨l[i], List.getElem_mem _, hp⟩
  split_ifs at hi with h1 h2
  · rw [PMF.support_map] at hi
    obtain ⟨r', hr', rfl⟩ := hi
    have ih := findKthElement_comparisons_le hr'
    have hm := hshort (fun a => decide (a < l[i])) (by simp)
    have := Nat.mul_le_mul hm hm
    simp only; nlinarith
  · rw [PMF.support_map] at hi
    obtain ⟨r', hr', rfl⟩ := hi
    have ih := findKthElement_comparisons_le hr'
    have hm := hshort (fun a => decide (l[i] < a)) (by simp)
    have := Nat.mul_le_mul hm hm
    simp only; nlinarith
  · rw [PMF.mem_support_pure_iff] at hi; subst hi
    have : 1 ≤ l.length := List.length_pos_iff.2 h
    simp only; nlinarith
termination_by l.length
decreasing_by
  all_goals
    exact List.length_filter_lt_length_iff_exists.2 ⟨l[i], List.getElem_mem _, by simp⟩

/-! ### Claim 7.4: expected number of comparisons -/

/-- `T(k, a₁, …, aₙ)`: the expected number of comparisons FindKthElement makes on this input.
[AB09, Claim 7.4] -/
noncomputable def expectedComparisons (k : ℕ) (l : List α) : ℝ≥0∞ :=
  ∑' r, findKthElement k l r * r.2

/-- `T(n)`: the maximum of `T(k, a₁, …, aₙ)` over all inputs with `n` entries from `α`.
[AB09, Claim 7.4] -/
noncomputable def maxExpectedComparisons (α : Type*) [LinearOrder α] (n : ℕ) : ℝ≥0∞ :=
  ⨆ (k : ℕ) (l : List α) (_ : l.length = n), expectedComparisons k l

/-- Expected second component of a distribution over runs. -/
private noncomputable def expCost {β : Type*} (p : PMF (β × ℕ)) : ℝ≥0∞ := ∑' r, p r * r.2

private lemma expCost_pure {β : Type*} (r : β × ℕ) : expCost (PMF.pure r) = r.2 := by
  simp [expCost, PMF.pure_apply, ite_mul]

private lemma expCost_bind {β γ : Type*} (p : PMF γ) (f : γ → PMF (β × ℕ)) :
    expCost (p.bind f) = ∑' a, p a * expCost (f a) := by
  simp only [expCost, PMF.bind_apply, ← ENNReal.tsum_mul_right, mul_assoc]
  rw [ENNReal.tsum_comm]
  simp only [ENNReal.tsum_mul_left]

private lemma expCost_map_add {β : Type*} (p : PMF (β × ℕ)) (n : ℕ) :
    expCost (p.map fun r => (r.1, r.2 + n)) = expCost p + n := by
  rw [← PMF.bind_pure_comp, expCost_bind]
  simp only [Function.comp_apply, expCost_pure, Nat.cast_add, mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rfl

/-- The length of the list FindKthElement recurses on after pivot `x` (`0` if it outputs `x`). -/
private def nextLength (k : ℕ) (l : List α) (x : α) : ℕ :=
  if k ≤ l.countP (· < x) then l.countP (· < x)
  else if l.countP (· ≤ x) < k then l.countP (x < ·) else 0

/-- The recurrence behind Claim 7.4: on a nonempty list,
`T(k, a) = n + (1/n) ∑ᵢ T(next call after pivot aᵢ)`. [AB09, Claim 7.4] -/
theorem expectedComparisons_eq {k : ℕ} {l : List α} (h : l ≠ []) :
    expectedComparisons k l = ∑ i : Fin l.length, (l.length : ℝ≥0∞)⁻¹ *
      (l.length + if k ≤ l.countP (· < l[i]) then expectedComparisons k (l.filter (· < l[i]))
        else if l.countP (· ≤ l[i]) < k then
          expectedComparisons (k - l.countP (· ≤ l[i])) (l.filter (l[i] < ·))
        else 0) := by
  haveI : Nonempty (Fin l.length) := ⟨⟨0, List.length_pos_iff.2 h⟩⟩
  have e : expectedComparisons k l = expCost (findKthElement k l) := rfl
  rw [e, findKthElement, dif_neg h, expCost_bind, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PMF.uniformOfFintype_apply, Fintype.card_fin]
  congr 1
  split_ifs
  · rw [expCost_map_add, add_comm]; rfl
  · rw [expCost_map_add, add_comm]; rfl
  · rw [expCost_pure, add_zero]

/-- `∑_{j<n} max j (n - 1 - j) ≤ 3n²/4`. -/
private lemma four_mul_sum_max_le (n : ℕ) :
    4 * ∑ j ∈ Finset.range n, max j (n - 1 - j) ≤ 3 * n ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | n + 2, ih =>
      have step : ∑ j ∈ Finset.range (n + 2), max j (n + 2 - 1 - j) =
          ∑ j ∈ Finset.range n, max j (n - 1 - j) + (3 * n + 2) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        have : ∀ j ∈ Finset.range n,
            max (j + 1) (n + 2 - 1 - (j + 1)) = max j (n - 1 - j) + 1 := by
          intro j hj
          simp only [Finset.mem_range] at hj
          rw [show n + 2 - 1 - (j + 1) = (n - 1 - j) + 1 by omega, Nat.succ_max_succ]
        rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
        simp; omega
      have := ih n (by omega)
      rw [step]; nlinarith

/-- `∑ᵢ max #{aⱼ < aᵢ} #{aⱼ > aᵢ} ≤ 3n²/4`: sort the list, then the entry at position `j` has
at most `j` entries below it and `n - 1 - j` above it. -/
private lemma four_mul_sum_max_countP_le (l : List α) :
    4 * (l.map fun x => max (l.countP (· < x)) (l.countP (x < ·))).sum ≤ 3 * l.length ^ 2 := by
  set s := l.insertionSort (· ≤ ·)
  have hp : s.Perm l := List.perm_insertionSort _ l
  have hs : s.Pairwise (· ≤ ·) := List.sorted_insertionSort _ l
  have hlen : s.length = l.length := List.length_insertionSort _ l
  let φ : α → ℕ := fun x => max (s.countP (· < x)) (s.countP (x < ·))
  have e1 : (l.map fun x => max (l.countP (· < x)) (l.countP (x < ·))).sum =
      ∑ i : Fin s.length, φ s[i.1] := by
    rw [Fin.sum_univ_fun_getElem, ← (hp.map _).sum_eq]
    simp only [φ, hp.countP_eq]
  have e2 : ∑ i : Fin s.length, φ s[i.1] ≤
      ∑ j ∈ Finset.range s.length, max j (s.length - 1 - j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => max j (s.length - 1 - j))]
    exact Finset.sum_le_sum fun i _ =>
      max_le_max (countP_lt_getElem_le hs i.2) (countP_getElem_lt_le hs i.2)
  calc 4 * (l.map fun x => max (l.countP (· < x)) (l.countP (x < ·))).sum
      ≤ 4 * ∑ j ∈ Finset.range s.length, max j (s.length - 1 - j) := by rw [e1]; omega
    _ ≤ 3 * s.length ^ 2 := four_mul_sum_max_le _
    _ = 3 * l.length ^ 2 := by rw [hlen]

/-- **Claim 7.4** for one input: FindKthElement makes at most `10 n` comparisons in
expectation on every input `k, a₁, …, aₙ`. [AB09, Claim 7.4]

**Proof sketch.** Induction on `n`, as in the book with `c = 1`. By the recurrence
`T(k, a) = n + (1/n) ∑ᵢ T(next call)` and the induction hypothesis, `T(k, a) ≤
n + (10/n) ∑ᵢ sᵢ`, where `sᵢ` is the length of the list recursed on after pivot `aᵢ`. That
list consists of the entries strictly below or strictly above `aᵢ`, so
`sᵢ ≤ max #{aⱼ < aᵢ} #{aⱼ > aᵢ}`; after sorting, the j-th pivot has at most `j - 1` entries
below and `n - j` above, and `∑_j max (j - 1) (n - j) ≤ 3n²/4`. Hence
`T(k, a) ≤ n + (10/n)(9n²/10) = 10 n`. -/
theorem expectedComparisons_le (k : ℕ) (l : List α) :
    expectedComparisons k l ≤ 10 * l.length := by
  by_cases h : l = []
  · subst h
    simp [expectedComparisons, findKthElement, PMF.pure_apply, ite_mul]
  have hn0 : l.length ≠ 0 := by simpa using h
  rw [expectedComparisons_eq h]
  -- each summand is at most `n + 10 · (length of the recursive list)`
  have hterm : ∀ i : Fin l.length, (l.length : ℝ≥0∞) + (if k ≤ l.countP (· < l[i]) then
      expectedComparisons k (l.filter (· < l[i]))
      else if l.countP (· ≤ l[i]) < k then
        expectedComparisons (k - l.countP (· ≤ l[i])) (l.filter (l[i] < ·))
      else 0) ≤ ((l.length + 10 * nextLength k l l[i] : ℕ) : ℝ≥0∞) := by
    intro i
    push_cast
    gcongr
    unfold nextLength
    split_ifs
    · have := expectedComparisons_le k (l.filter (· < l[i]))
      rwa [← List.countP_eq_length_filter] at this
    · have := expectedComparisons_le (k - l.countP (· ≤ l[i])) (l.filter (l[i] < ·))
      rwa [← List.countP_eq_length_filter] at this
    · simp
  -- the arithmetic: `∑ᵢ (n + 10 sᵢ) ≤ 10 n²`
  have hsum : ∑ i : Fin l.length, (l.length + 10 * nextLength k l l[i]) ≤
      l.length * (10 * l.length) := by
    have h1 : ∑ i : Fin l.length, nextLength k l l[i] ≤
        (l.map fun x => max (l.countP (· < x)) (l.countP (x < ·))).sum := by
      rw [← Fin.sum_univ_fun_getElem]
      refine Finset.sum_le_sum fun i _ => ?_
      unfold nextLength; split_ifs <;> simp
    have h2 := four_mul_sum_max_countP_le l
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.mul_sum, smul_eq_mul]
    nlinarith
  calc _ ≤ ∑ i : Fin l.length, (l.length : ℝ≥0∞)⁻¹ *
          ((l.length + 10 * nextLength k l l[i] : ℕ) : ℝ≥0∞) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_left' (hterm i) _
    _ = (l.length : ℝ≥0∞)⁻¹ *
          ((∑ i : Fin l.length, (l.length + 10 * nextLength k l l[i]) : ℕ) : ℝ≥0∞) := by
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ (l.length : ℝ≥0∞)⁻¹ * ((l.length * (10 * l.length) : ℕ) : ℝ≥0∞) := by gcongr
    _ = 10 * l.length := by
        rw [Nat.cast_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by simpa using hn0)
          (ENNReal.natCast_ne_top _), one_mul]
        norm_cast
termination_by l.length
decreasing_by
  all_goals
    exact List.length_filter_lt_length_iff_exists.2 ⟨l[i], List.getElem_mem _, by simp⟩

/-- **Claim 7.4.** `T(n) ≤ 10 n`: the expected number of comparisons of FindKthElement is at
most `10 n` on every input of length `n`, so `T(n) = O(n)`. [AB09, Claim 7.4] -/
theorem maxExpectedComparisons_le (n : ℕ) : maxExpectedComparisons α n ≤ 10 * n := by
  refine iSup₂_le fun k l => iSup_le fun hl => ?_
  rw [← hl]; exact expectedComparisons_le k l

end Randomized
