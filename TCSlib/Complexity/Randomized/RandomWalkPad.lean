/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.RandomWalkHitting
import TCSlib.Complexity.Randomized.Fingerprint
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Size

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Padding an undirected graph to a regular multigraph

[AB09, Exercise 7.11(e)] (p.142): adding parallel self-loops makes any undirected graph on `n`
vertices regular. We pad to degree `D ≥ n` by slot indexing — slot `i` of `v` leads to vertex
`i` if `i < n` and `i` is a neighbour of `v`, and back to `v` otherwise — and choose
`D = 2^{size n} ∈ [n, 2n]`, so one step costs `size n = ⌈log₂(n+1)⌉` fair coins. Combined
with `TCSlib.Complexity.Randomized.RandomWalkHitting`, this is the probabilistic content of
[AB09, Theorem 7.19] (`UPATH ∈ RL`, p.139) as a coin-word statement.

## Main definitions

* `Randomized.padGraph` — the self-loop padding of a symmetric relation on `Fin n` to a
  `D`-regular multigraph, `n ≤ D`.
* `Randomized.padDegree` — the degree `2^{size n}`.

## Main results

* `Randomized.padGraph_reflTransGen_iff` — padding preserves reachability.
* `Randomized.three_quarters_le_randProb_padWalk` — if `s` reaches `t`, a `100n⁴`-step walk on
  the padded graph driven by fair coins visits `t` with probability `≥ 3/4`
  [AB09, Theorem 7.19].
* `Randomized.randProb_padWalk_eq_zero` — if `s` does not reach `t`, it never does.

## Divergences

* [AB09, Exercise 7.11(e)] transfers a hitting probability from the (possibly irregular)
  graph `G` to its regular padding `G'`: a `k`-step bound `0.9` in `G` becomes a `10n²k`-step
  bound `1/2` in `G'`. That transfer is `Randomized.half_le_hitProb_padGraph`
  (`TCSlib.Complexity.Randomized.RandomWalkMixingPad`); the route here does not use it, since
  the hitting-time bound of `TCSlib.Complexity.Randomized.RandomWalkHitting` is proved for the
  padded multigraph directly, which is all [AB09, Theorem 7.19] needs.
* The graph is a symmetric relation `r` on `Fin n`; loops of `r` are harmless.
* The RL algorithm's walk is the walk on `padGraph`: a self-loop slot counts as a step, as in
  the book's Exercise 7.11(e) route.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset

variable {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r]

/-- The padded neighbour function: slot `i` of `v` leads to vertex `i` when `i < n` and `r v i`,
and is a self-loop at `v` otherwise. -/
def padNbr {D : ℕ} (v : Fin n) (i : Fin D) : Fin n :=
  if h : (i : ℕ) < n then (if r v ⟨i, h⟩ then ⟨i, h⟩ else v) else v

/-- Off the diagonal, slot `i` of `u` leads to `v` exactly when `i = v` and `r u v`. -/
theorem padNbr_eq_iff {D : ℕ} {u v : Fin n} (huv : u ≠ v) (i : Fin D) :
    padNbr r u i = v ↔ (i : ℕ) = v ∧ r u v := by
  unfold padNbr
  split_ifs with h hr
  · constructor
    · intro hi
      exact ⟨congrArg Fin.val hi, hi ▸ hr⟩
    · rintro ⟨hi, -⟩
      exact Fin.ext hi
  · constructor
    · intro hi; exact absurd hi huv
    · rintro ⟨hi, hr'⟩
      have heq : (⟨i, h⟩ : Fin n) = v := by ext; exact hi
      rw [← heq] at hr'
      exact absurd hr' hr
  · constructor
    · intro hi; exact absurd hi huv
    · rintro ⟨hi, -⟩
      exact absurd (hi ▸ v.2) h

/-- Off the diagonal, the padded multiplicity is `1` on edges of `r` and `0` otherwise. -/
theorem card_padNbr_eq {D : ℕ} (hD : n ≤ D) {u v : Fin n} (huv : u ≠ v) :
    (univ.filter fun i : Fin D => padNbr r u i = v).card = if r u v then 1 else 0 := by
  rw [Finset.filter_congr fun i _ => padNbr_eq_iff r huv i]
  split_ifs with h
  · refine Finset.card_eq_one.mpr ⟨⟨v, lt_of_lt_of_le v.2 hD⟩, ?_⟩
    ext i
    simp [h, Fin.ext_iff]
  · simp [h]

/-- **Self-loop padding** [AB09, Exercise 7.11(e)]: a symmetric relation `r` on `Fin n` padded
with parallel self-loops to a `D`-regular multigraph, `n ≤ D`. -/
def padGraph (hr : Symmetric r) (D : ℕ) (hD : n ≤ D) : RegularMultigraph (Fin n) D where
  nbr := padNbr r
  mult_symm u v := by
    by_cases huv : u = v
    · subst huv; rfl
    · rw [card_padNbr_eq r hD huv, card_padNbr_eq r hD (Ne.symm huv)]
      exact if_congr ⟨fun h => hr h, fun h => hr h⟩ rfl rfl

variable {r}

/-- Adjacency in the padded graph is `r` plus a loop at every vertex. -/
theorem padGraph_adj_iff (hr : Symmetric r) {D : ℕ} (hD : n ≤ D) {u v : Fin n} :
    (padGraph r hr D hD).Adj u v ↔ u = v ∨ r u v := by
  constructor
  · rintro ⟨i, hi⟩
    by_cases huv : u = v
    · exact Or.inl huv
    · exact Or.inr ((padNbr_eq_iff r huv i).mp hi).2
  · rintro (rfl | h)
    · refine ⟨⟨u, lt_of_lt_of_le u.2 hD⟩, ?_⟩
      show padNbr r u _ = u
      unfold padNbr
      simp
    · by_cases huv : u = v
      · subst huv
        refine ⟨⟨u, lt_of_lt_of_le u.2 hD⟩, ?_⟩
        show padNbr r u _ = u
        unfold padNbr
        simp
      · exact ⟨⟨v, lt_of_lt_of_le v.2 hD⟩, (padNbr_eq_iff r huv _).mpr ⟨rfl, h⟩⟩

/-- Padding preserves reachability [AB09, Exercise 7.11(e)]. -/
theorem padGraph_reflTransGen_iff (hr : Symmetric r) {D : ℕ} (hD : n ≤ D) {s t : Fin n} :
    Relation.ReflTransGen (padGraph r hr D hD).Adj s t ↔ Relation.ReflTransGen r s t := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih =>
      rcases (padGraph_adj_iff hr hD).mp hab with rfl | h
      · exact ih
      · exact ih.tail h
  · exact Relation.ReflTransGen.mono fun a b h => (padGraph_adj_iff hr hD).mpr (Or.inr h)

/-- The padding degree `2^{size n}`, the least power of two exceeding `n`. -/
def padDegree (n : ℕ) : ℕ := 2 ^ Nat.size n

/-- The padding degree is at least `n`. -/
theorem le_padDegree (n : ℕ) : n ≤ padDegree n := (Nat.lt_size_self n).le

/-- The padding degree is at most `2n` for `n ≥ 1`. -/
theorem padDegree_le (hn : 0 < n) : padDegree n ≤ 2 * n := by
  unfold padDegree
  have hs : 0 < Nat.size n := Nat.size_pos.mpr hn
  have h : 2 ^ (Nat.size n - 1) ≤ n := by
    by_contra h
    push_neg at h
    exact absurd (Nat.size_le.mpr h) (by omega)
  calc 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
        rw [← pow_succ']; congr 1; omega
    _ ≤ 2 * n := by omega

instance (n : ℕ) : NeZero (padDegree n) := ⟨pow_ne_zero _ two_ne_zero⟩

/-- **[AB09, Theorem 7.19], coin form.** If `s` reaches `t` in the undirected graph `r` on `n`
vertices, the random walk of length `100n⁴` on the padded graph, reading `size n` fair coins
per step through any bijection `e` (e.g. `Randomized.bitsEquiv`), visits `t` with probability
at least `3/4`. -/
theorem three_quarters_le_randProb_padWalk (hr : Symmetric r) {s t : Fin n}
    (hst : Relation.ReflTransGen r s t) (e : (Fin (Nat.size n) → Bool) ≃ Fin (padDegree n)) :
    3 / 4 ≤ randProb (100 * n ^ 4 * Nat.size n) (fun l =>
      (padGraph r hr _ (le_padDegree n)).hits t s (decodeIdx e (100 * n ^ 4) l) = true) := by
  rw [RegularMultigraph.randProb_hits_decodeIdx]
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) s.2
  have hD : padDegree n ≤ 2 * Fintype.card (Fin n) := by
    rw [Fintype.card_fin]; exact padDegree_le hn
  have h := (padGraph r hr _ (le_padDegree n)).three_quarters_le_hitProb hD
    ((padGraph_reflTransGen_iff hr _).mpr hst)
  simpa only [Fintype.card_fin] using h

/-- If `s` does not reach `t`, the padded walk never visits `t`: acceptance probability `0`. -/
theorem randProb_padWalk_eq_zero (hr : Symmetric r) {s t : Fin n}
    (hst : ¬ Relation.ReflTransGen r s t) {b D : ℕ} (hD : n ≤ D) (e : (Fin b → Bool) ≃ Fin D)
    (k : ℕ) :
    randProb (k * b) (fun l => (padGraph r hr D hD).hits t s (decodeIdx e k l) = true) = 0 := by
  have : NeZero D := ⟨fun h0 => absurd (h0 ▸ hD) (by
    intro h; exact absurd (lt_of_lt_of_le s.2 h) (Nat.not_lt_zero _))⟩
  rw [RegularMultigraph.randProb_hits_decodeIdx]
  exact (padGraph r hr D hD).hitProb_eq_zero_of_not_reachable
    (fun h => hst ((padGraph_reflTransGen_iff hr hD).mp h)) k

end Randomized
