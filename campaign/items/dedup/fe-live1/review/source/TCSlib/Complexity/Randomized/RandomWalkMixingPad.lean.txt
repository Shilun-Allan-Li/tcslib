/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.RandomWalkPad
import TCSlib.Complexity.Randomized.DirectedWalk

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hitting probabilities survive self-loop padding

[AB09, Exercise 7.11(e)] (p.142): let `G` be an `n`-vertex graph, not necessarily regular, and
`G'` the regular graph obtained by adding parallel self-loops. If a `k`-step random walk in `G`
from `s` hits `t` with probability at least `0.9`, then a `10n²k`-step random walk in `G'` from
`s` hits `t` with probability at least `1/2`.

## Main definitions

None new: the walk on `G` is `Randomized.hitProb (Digraph.mk r)` of
`TCSlib.Complexity.Randomized.DirectedWalk` (uniform neighbour at each step), and `G'` is
`Randomized.padGraph`.

## Main results

* `Randomized.half_le_hitProb_padGraph` — [AB09, Exercise 7.11(e)] for `G' = padGraph r D`,
  any padding degree `n ≤ D ≤ 4n²`.
* `Randomized.half_le_hitProb_padDegree` — the same for the RL padding degree `padDegree n`.

## Divergences

* The walk on the irregular `G` has no fixed-size uniform sample space; its hitting probability
  is `Randomized.hitProb (Digraph.mk r)`, defined by the first-step recursion of its law. An
  isolated vertex keeps the walk in place.
* The book leaves the padded degree free ("a sufficient number" of loops). `G'` is
  `Randomized.padGraph r D` for any `n ≤ D ≤ 4n²`, which covers the RL padding
  `padDegree n ≤ 2n`; the constant `10n²` needs `D ≤ 4n²`, since a step of `G'` from a
  non-isolated vertex is a step of `G` with probability `≥ 1/D`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset

variable {n : ℕ} {r : Fin n → Fin n → Prop} [DecidableRel r]

/-- The walk's hitting probabilities lie in `[0, 1]`. -/
private theorem hitProb_mk_mem_Icc (t : Fin n) :
    ∀ k s, 0 ≤ hitProb (Digraph.mk r) t k s ∧ hitProb (Digraph.mk r) t k s ≤ 1
  | 0, s => by simp only [hitProb]; split_ifs <;> norm_num
  | k + 1, s => by
    have ih := fun u => hitProb_mk_mem_Icc t k u
    simp only [hitProb, avgOut]
    split_ifs with h1 h2
    · norm_num
    · refine ⟨div_nonneg (Finset.sum_nonneg fun u _ => (ih u).1) (Nat.cast_nonneg _), ?_⟩
      rw [div_le_one (by exact_mod_cast h2.card_pos)]
      calc ∑ u ∈ outNbrs (Digraph.mk r) s, hitProb (Digraph.mk r) t k u
          ≤ ∑ _u ∈ outNbrs (Digraph.mk r) s, (1 : ℚ) := Finset.sum_le_sum fun u _ => (ih u).2
        _ = (outNbrs (Digraph.mk r) s).card := by simp
    · exact ih s

/-- From an isolated vertex `s ≠ t` the walk never reaches `t`. -/
private theorem hitProb_mk_eq_zero {s t : Fin n} (hst : s ≠ t)
    (h0 : (outNbrs (Digraph.mk r) s).card = 0) : ∀ k, hitProb (Digraph.mk r) t k s = 0
  | 0 => by simp [hitProb, hst]
  | k + 1 => by
    have hne : ¬ (outNbrs (Digraph.mk r) s).Nonempty := by
      rw [← Finset.card_pos]; omega
    simp only [hitProb, if_neg hst, avgOut, if_neg hne]
    exact hitProb_mk_eq_zero hst h0 k

/-- First-step form at a vertex `s ≠ t` with neighbours. -/
private theorem hitProb_mk_succ {s t : Fin n} (hst : s ≠ t)
    (hpos : 0 < (outNbrs (Digraph.mk r) s).card) (k : ℕ) :
    hitProb (Digraph.mk r) t (k + 1) s = (∑ u ∈ outNbrs (Digraph.mk r) s,
      hitProb (Digraph.mk r) t k u) / (outNbrs (Digraph.mk r) s).card := by
  simp only [hitProb, if_neg hst, avgOut, if_pos (Finset.card_pos.mp hpos)]

variable (r) in
/-- The slots of `s` in the padding: one to each neighbour, the other `D − deg s` loops. -/
theorem sum_padNbr {D : ℕ} (hD : n ≤ D) (f : Fin n → ℚ) (s : Fin n) :
    ∑ i : Fin D, f (padNbr r s i) =
      ∑ u ∈ univ.filter (r s), f u + ((D : ℚ) - (univ.filter (r s)).card) * f s := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hD
  rw [Fin.sum_univ_add]
  have h1 : ∀ u : Fin n, padNbr r s (Fin.castAdd c u) = if r s u then u else s := fun u => by
    simp [padNbr]
  have h2 : ∀ j : Fin c, padNbr r s (Fin.natAdd n j) = s := fun j => by
    simp [padNbr]
  simp only [h1, h2, apply_ite f, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin]
  have hcard := Finset.filter_card_add_filter_neg_card_eq_card (s := univ) (r s)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have : ((univ.filter fun u => ¬ r s u).card : ℚ) = n - (univ.filter (r s)).card := by
    have h := congrArg (Nat.cast : ℕ → ℚ) hcard
    push_cast at h
    linarith
  rw [this]
  push_cast
  ring

/-- `Pr[Bin(m, 1/D) < j]`: fewer than `j` successes in `m` independent trials of success
probability `1/D`. -/
private def binTail (D : ℕ) : ℕ → ℕ → ℚ
  | _, 0 => 0
  | 0, _ + 1 => 1
  | m + 1, j + 1 => binTail D m j / D + (1 - 1 / D) * binTail D m (j + 1)

section binTail

variable {D : ℕ} (hD : 1 ≤ D)
include hD

private theorem one_div_mem : 0 < (1 : ℚ) / D ∧ (1 : ℚ) / D ≤ 1 := by
  have : (1 : ℚ) ≤ D := by exact_mod_cast hD
  exact ⟨by positivity, (div_le_one (by linarith)).mpr this⟩

private theorem binTail_mem_Icc : ∀ m j, 0 ≤ binTail D m j ∧ binTail D m j ≤ 1
  | _, 0 => by simp [binTail]
  | 0, _ + 1 => by simp [binTail]
  | m + 1, j + 1 => by
    have h1 := binTail_mem_Icc m j
    have h2 := binTail_mem_Icc m (j + 1)
    obtain ⟨hp0, hp1⟩ := one_div_mem hD
    simp only [binTail, div_eq_mul_one_div (binTail D m j)]
    constructor <;> nlinarith

private theorem binTail_mono : ∀ m j, binTail D m j ≤ binTail D m (j + 1)
  | m, 0 => by simp only [binTail]; exact (binTail_mem_Icc hD m 1).1
  | 0, _ + 1 => le_rfl
  | m + 1, j + 1 => by
    have h1 := binTail_mono m j
    have h2 := binTail_mono m (j + 1)
    obtain ⟨hp0, hp1⟩ := one_div_mem hD
    simp only [binTail, div_eq_mul_one_div (binTail D m _)]
    nlinarith

private theorem binTail_succ_le : ∀ m j, binTail D (m + 1) j ≤ binTail D m j
  | _, 0 => by simp [binTail]
  | m, j + 1 => by
    have h1 := binTail_mono hD m j
    obtain ⟨hp0, hp1⟩ := one_div_mem hD
    simp only [binTail, div_eq_mul_one_div (binTail D m _)]
    nlinarith

/-- The expected waiting time: `∑_{m<M} Pr[Bin(m, 1/D) < j] ≤ j·D`. -/
private theorem sum_binTail_le : ∀ M j, ∑ m ∈ range M, binTail D m j ≤ j * D
  | 0, j => by simp; positivity
  | M + 1, 0 => by simp [binTail]
  | M + 1, j + 1 => by
    have h1 := sum_binTail_le M j
    have h2 := sum_binTail_le M (j + 1)
    have hD' : (1 : ℚ) ≤ D := by exact_mod_cast hD
    rw [Finset.sum_range_succ']
    simp only [binTail, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    have hq : 0 ≤ 1 - (1 : ℚ) / D := sub_nonneg.mpr (one_div_mem hD).2
    calc (∑ m ∈ range M, binTail D m j) / D + (1 - 1 / D) * ∑ m ∈ range M, binTail D m (j + 1)
          + 1
        ≤ j * D / D + (1 - 1 / D) * ((j + 1 : ℕ) * D) + 1 := by
          gcongr
      _ = (j + 1 : ℕ) * D := by field_simp; push_cast; ring

/-- Markov's inequality: `(L + 1)·Pr[Bin(L, 1/D) < j] ≤ j·D`. -/
private theorem succ_mul_binTail_le (L j : ℕ) : (L + 1 : ℚ) * binTail D L j ≤ j * D := by
  have hanti : ∀ m ∈ range (L + 1), binTail D L j ≤ binTail D m j := fun m hm =>
    antitone_nat_of_succ_le (f := fun m => binTail D m j) (fun m => binTail_succ_le hD m j)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
  calc (L + 1 : ℚ) * binTail D L j = ∑ _m ∈ range (L + 1), binTail D L j := by simp
    _ ≤ ∑ m ∈ range (L + 1), binTail D m j := Finset.sum_le_sum hanti
    _ ≤ j * D := sum_binTail_le hD _ _

end binTail

/-- **Domination of the padded walk.** In `m` steps the padded walk hits `t` at least as often as
the `j`-step walk on `r`, up to the probability `Pr[Bin(m, 1/D) < j]` of making fewer than `j`
real moves.

**Proof sketch.** Induct on `m`. At `s ≠ t` with `d = deg s ≥ 1`, a padded step moves to each
neighbour with probability `1/D` and stays with probability `1 − d/D`; by induction the result
is at least `R − (d·b₁ + (D − d)·b₂)/D`, where `R` is the walk's `(j+1)`-step value and
`b₁ ≤ b₂` are the tails for `j` and `j + 1`. Since `d ≥ 1`, this is `≥ R − (b₁ + (D−1)·b₂)/D`. -/
private theorem sub_binTail_le_hitProb (hr : Symmetric r) {D : ℕ} (hD : n ≤ D) (t : Fin n) :
    ∀ m j s, hitProb (Digraph.mk r) t j s - binTail D m j ≤ (padGraph r hr D hD).hitProb t m s := by
  have hD1 : ∀ s : Fin n, 1 ≤ D := fun s => le_trans (Nat.one_le_iff_ne_zero.mpr
    (by intro h; exact absurd s.2 (by omega))) hD
  intro m
  induction m with
  | zero =>
    intro j s
    have hNe : NeZero D := ⟨by have := hD1 s; omega⟩
    cases j with
    | zero =>
      simp only [hitProb, binTail, sub_zero, RegularMultigraph.hitProb_zero]
      exact le_rfl
    | succ j =>
      simp only [binTail]
      linarith [(hitProb_mk_mem_Icc (r := r) t (j + 1) s).2,
        (padGraph r hr D hD).hitProb_nonneg t 0 s]
  | succ m ih =>
    intro j s
    have hNe : NeZero D := ⟨by have := hD1 s; omega⟩
    set G := padGraph r hr D hD
    have hDq : (1 : ℚ) ≤ D := by exact_mod_cast hD1 s
    have hsucc : G.hitProb t (m + 1) s =
        if s = t then 1 else (∑ i, G.hitProb t m (padNbr r s i)) / D :=
      G.hitProb_succ t m s
    by_cases hst : s = t
    · rw [hsucc, if_pos hst]
      linarith [(hitProb_mk_mem_Icc (r := r) t j s).2, (binTail_mem_Icc (hD1 s) (m + 1) j).1]
    rw [hsucc, if_neg hst]
    cases j with
    | zero =>
      simp only [hitProb, if_neg hst, binTail, sub_zero]
      exact div_nonneg (Finset.sum_nonneg fun i _ => G.hitProb_nonneg t m _) (by positivity)
    | succ j =>
      rcases Nat.eq_zero_or_pos (outNbrs (Digraph.mk r) s).card with h0 | hpos
      · rw [hitProb_mk_eq_zero hst h0 (j + 1)]
        have hnn : 0 ≤ (∑ i : Fin D, G.hitProb t m (padNbr r s i)) / D :=
          div_nonneg (Finset.sum_nonneg fun i _ => G.hitProb_nonneg t m _) (by positivity)
        linarith [(binTail_mem_Icc (hD1 s) (m + 1) (j + 1)).1]
      set d : ℚ := ((outNbrs (Digraph.mk r) s).card : ℚ)
      set R := hitProb (Digraph.mk r) t (j + 1) s
      set b₁ := binTail D m j
      set b₂ := binTail D m (j + 1)
      have hd1 : (1 : ℚ) ≤ d := by
        rw [show d = ((outNbrs (Digraph.mk r) s).card : ℚ) from rfl]; exact_mod_cast hpos
      have hdD : d ≤ D := by
        have : (outNbrs (Digraph.mk r) s).card ≤ n := (Finset.card_le_univ _).trans (by simp)
        rw [show d = ((outNbrs (Digraph.mk r) s).card : ℚ) from rfl]
        exact_mod_cast this.trans hD
      have hR : ∑ u ∈ outNbrs (Digraph.mk r) s, hitProb (Digraph.mk r) t j u = d * R := by
        simp only [R, d]
        rw [hitProb_mk_succ hst hpos j]
        field_simp
      have hb : b₁ ≤ b₂ := binTail_mono (hD1 s) m j
      have hlow : d * R - d * b₁ + (D - d) * (R - b₂) ≤
          ∑ i : Fin D, G.hitProb t m (padNbr r s i) := by
        rw [sum_padNbr r hD]
        have h1 : ∑ u ∈ outNbrs (Digraph.mk r) s, (hitProb (Digraph.mk r) t j u - b₁) ≤
            ∑ u ∈ outNbrs (Digraph.mk r) s, G.hitProb t m u :=
          Finset.sum_le_sum fun u _ => ih j u
        rw [Finset.sum_sub_distrib, hR, Finset.sum_const] at h1
        simp only [nsmul_eq_mul] at h1
        have h2 := mul_le_mul_of_nonneg_left (ih (j + 1) s) (sub_nonneg.mpr hdD)
        exact add_le_add h1 h2
      simp only [binTail]
      rw [le_div_iff₀ (by linarith)]
      have : (d - 1) * (b₁ - b₂) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have hdiv : (b₁ / D + (1 - 1 / D) * b₂) * D = b₁ + (D - 1) * b₂ := by
        field_simp
      nlinarith [hdiv]

/-- **[AB09, Exercise 7.11(e)].** Let `r` be an `n`-vertex undirected graph and `G'` its padding
to a `D`-regular multigraph by self-loops, `n ≤ D ≤ 4n²`. If a `k`-step random walk in `r` from
`s` hits `t` with probability at least `0.9`, then a `10n²k`-step random walk in `G'` from `s`
hits `t` with probability at least `1/2`. -/
theorem half_le_hitProb_padGraph (hr : Symmetric r) {D : ℕ} (hD : n ≤ D) (hD' : D ≤ 4 * n ^ 2)
    {s t : Fin n} {k : ℕ} (h : 9 / 10 ≤ hitProb (Digraph.mk r) t k s) :
    1 / 2 ≤ (padGraph r hr D hD).hitProb t (10 * n ^ 2 * k) s := by
  have hD1 : 1 ≤ D := le_trans (by have := s.2; omega) hD
  have hlow := sub_binTail_le_hitProb hr hD t (10 * n ^ 2 * k) k s
  have hmk := succ_mul_binTail_le hD1 (10 * n ^ 2 * k) k
  have hb0 := (binTail_mem_Icc hD1 (10 * n ^ 2 * k) k).1
  have hDq : (D : ℚ) ≤ 4 * n ^ 2 := by exact_mod_cast hD'
  set b := binTail D (10 * n ^ 2 * k) k
  have hX : (0 : ℚ) ≤ n ^ 2 * k := by positivity
  push_cast at hmk
  have hkD : (k : ℚ) * D ≤ 4 * (n ^ 2 * k) := by nlinarith [hDq, (Nat.cast_nonneg k : (0 : ℚ) ≤ k)]
  have hb : b ≤ 2 / 5 := by nlinarith
  linarith

/-- **[AB09, Exercise 7.11(e)] for the RL padding.** With `D = padDegree n` (`≤ 2n`): a
`0.9`-likely `k`-step hit in `r` gives a `1/2`-likely `10n²k`-step hit in the padded graph. -/
theorem half_le_hitProb_padDegree (hr : Symmetric r) {s t : Fin n} {k : ℕ}
    (h : 9 / 10 ≤ hitProb (Digraph.mk r) t k s) :
    1 / 2 ≤ (padGraph r hr _ (le_padDegree n)).hitProb t (10 * n ^ 2 * k) s := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) s.2
  refine half_le_hitProb_padGraph hr _ ?_ h
  have := padDegree_le hn
  nlinarith

end Randomized
