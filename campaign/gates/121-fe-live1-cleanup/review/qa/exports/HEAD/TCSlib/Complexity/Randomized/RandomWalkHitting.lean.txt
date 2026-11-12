/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.RandomWalk
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.Order.Archimedean.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hitting times of random walks on regular multigraphs

The analysis behind [AB09, Theorem 7.19] (p.139), following [AB09, Exercise 7.11] (p.142): on
a `D`-regular undirected multigraph with `n` vertices, a random walk from `s` reaches any `t`
connected to `s` in expected time at most `2·D·n³`; with `D ≤ 2n` this is `≤ 4n⁴ ≤ 10n⁴`, and
a walk of length `100n⁴` visits `t` with probability at least `3/4`. Exercise 7.11(d) as
printed is proved separately: `E_{u,v} ≤ k·D·(n − 1) ≤ 100kn²` along a path of length `k`.

Expected times are finite tail sums: `hitTime t N s = ∑_{j<N} Pr[the j-step walk from s
avoids t]`, the expectation of `min(τ, N)` for the hitting time `τ`; a bound uniform in `N` is
a bound on `𝔼[τ]`.

## Main definitions

* `Randomized.RegularMultigraph.hitTime` — the truncated expected hitting time.
* `Randomized.RegularMultigraph.returnTime` — the truncated expected return time.

## Main results

* `Randomized.RegularMultigraph.returnTime_le_card` — Kac's bound `E_u ≤ n`
  [AB09, Exercise 7.11(c)].
* `Randomized.RegularMultigraph.hitTime_le` — `𝔼[τ_t] ≤ 2·D·n³` from any connected `s`.
* `Randomized.RegularMultigraph.hitTime_le_add` — the triangle inequality for hitting times.
* `Randomized.RegularMultigraph.hitTime_le_hundred_mul` — `E_{u,v} ≤ 100kn²` along a path of
  length `≤ k` [AB09, Exercise 7.11(d)].
* `Randomized.RegularMultigraph.missProb_thousand_mul_pow_three_le` — a `1000n³`-step walk
  misses a connected `t` with probability `≤ 1/10` [AB09, Exercise 7.11(d)].
* `Randomized.RegularMultigraph.hitTime_le_ten_mul_pow_four` — `𝔼[τ_t] ≤ 10n⁴` when
  `D ≤ 2n` [AB09, §7.7, p.139].
* `Randomized.RegularMultigraph.three_quarters_le_hitProb` — a `100n⁴`-step walk visits `t`
  with probability `≥ 3/4` [AB09, Theorem 7.19].

## Divergences

* [AB09, Exercise 7.11(d)] is stated for a regular graph; for a multigraph we add the
  hypothesis `D ≤ 100n` (a simple graph with loops has `D ≤ n`; the padded graphs used by
  `UPATH` have `D = padDegree n ≤ 2n` by `Randomized.padDegree_le`). Without it the bound
  fails: for fixed `n`, `E_{u,v}` grows with `D`, since self-loops make each step leave a
  vertex with probability `O(1/D)` (on the 3-vertex path, `E_{a,c} ≥ D`). A path is a
  walk in `SimpleGraph.fromRel G.Adj`. The proof chains `E_{x,y} ≤ D·(E_y⁺ − 1) ≤ D·(n − 1)`
  over the edges of the path by `hitTime_le_add` (first passage, proved on truncated tail
  sums via `hitTime_sub_le` and Markov), giving `k·D·(n − 1)`.
* The `10n⁴`/`100n⁴` of p.139 are derived from the cruder `hitTime_le` (`2·D·n³`, an energy
  argument). Kac's bound is proved as `E_u ≤ n`, sharper than `10n`.
* Exercise 7.11(b) (convergence to the uniform distribution) is not used by this route; it is
  in `TCSlib.Complexity.Randomized.RandomWalkMixing` (with
  `TCSlib.Complexity.Randomized.RandomWalkCover`). Exercise 7.11(e) is in
  `TCSlib.Complexity.Randomized.RandomWalkMixingPad`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

namespace RegularMultigraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {D : ℕ} [NeZero D]
  (G : RegularMultigraph V D)

omit [Fintype V] [NeZero D] in
/-- Averaging is monotone. -/
theorem avg_mono {f g : V → ℚ} (h : ∀ v, f v ≤ g v) (s : V) : G.avg f s ≤ G.avg g s :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun _ _ => h _) (Nat.cast_nonneg D)

omit [Fintype V] in
/-- The average of the constant `c` is `c`. -/
theorem avg_const (c : ℚ) (s : V) : G.avg (fun _ => c) s = c := by
  have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  simp only [avg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- A walk starting at `t` never avoids `t`. -/
theorem missProb_self (t : V) (k : ℕ) : G.missProb t k t = 0 := by
  cases k with
  | zero => simp [missProb, hitProb_zero]
  | succ k => rw [missProb_succ, if_pos rfl]

omit [Fintype V] [NeZero D] in
/-- A `0`-step walk from `s ≠ t` avoids `t`. -/
theorem missProb_zero_of_ne {t s : V} (hs : s ≠ t) : G.missProb t 0 s = 1 := by
  simp [missProb, hitProb_zero, hs]

/-- Avoiding `t` for `k + 1` steps is no likelier than for `k` steps. -/
theorem missProb_succ_le (t : V) (k : ℕ) (s : V) : G.missProb t (k + 1) s ≤ G.missProb t k s := by
  induction k generalizing s with
  | zero =>
    by_cases hs : s = t
    · subst hs; rw [missProb_self, missProb_self]
    · rw [missProb_succ, if_neg hs, G.missProb_zero_of_ne hs]
      calc G.avg (G.missProb t 0) s ≤ G.avg (fun _ => 1) s :=
            G.avg_mono (fun v => (G.missProb_mem_Icc t 0 v).2) s
        _ = 1 := G.avg_const 1 s
  | succ k ih =>
    by_cases hs : s = t
    · subst hs; rw [missProb_self, missProb_self]
    · rw [missProb_succ, if_neg hs, missProb_succ, if_neg hs]
      exact G.avg_mono ih s

/-- The miss probability is antitone in the walk length. -/
theorem missProb_antitone (t s : V) : Antitone fun k => G.missProb t k s :=
  antitone_nat_of_succ_le fun k => G.missProb_succ_le t k s

omit [Fintype V] [NeZero D] in
/-- If `s` is not connected to `t`, no walk from `s` visits `t`. -/
theorem hitProb_eq_zero_of_not_reachable {t s : V} (h : ¬ Relation.ReflTransGen G.Adj s t)
    (k : ℕ) : G.hitProb t k s = 0 := by
  unfold hitProb idxProb
  rw [Finset.filter_false_of_mem fun w _ hw => h (G.reflTransGen_of_hits s _ hw)]
  simp

/-- The truncated expected hitting time `∑_{j<N} Pr[the j-step walk from s avoids t]`,
i.e. `𝔼[min(τ_t, N)]` for the first visit time `τ_t` of `t`. -/
def hitTime (t : V) (N : ℕ) (s : V) : ℚ := ∑ j ∈ range N, G.missProb t j s

omit [Fintype V] in
/-- Truncated hitting times are nonnegative. -/
theorem hitTime_nonneg (t : V) (N : ℕ) (s : V) : 0 ≤ G.hitTime t N s :=
  Finset.sum_nonneg fun j _ => (G.missProb_mem_Icc t j s).1

/-- The hitting time of `t` from `t` is `0`. -/
theorem hitTime_self (t : V) (N : ℕ) : G.hitTime t N t = 0 :=
  Finset.sum_eq_zero fun j _ => G.missProb_self t j

omit [Fintype V] in
/-- Truncated hitting times grow with the truncation. -/
theorem hitTime_le_succ (t : V) (N : ℕ) (s : V) : G.hitTime t N s ≤ G.hitTime t (N + 1) s := by
  unfold hitTime
  rw [Finset.sum_range_succ]
  linarith [(G.missProb_mem_Icc t N s).1]

/-- First-step analysis: `hitTime t (N+1) s = 1 + avg (hitTime t N) s` for `s ≠ t`. -/
theorem hitTime_succ {t s : V} (hs : s ≠ t) (N : ℕ) :
    G.hitTime t (N + 1) s = 1 + G.avg (G.hitTime t N) s := by
  unfold hitTime avg
  rw [Finset.sum_range_succ', G.missProb_zero_of_ne hs, add_comm, Finset.sum_comm,
    Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [missProb_succ, if_neg hs, avg]

/-- Off `t`, the truncated hitting time exceeds its neighbour average by at most one. -/
theorem hitTime_sub_avg_le {t s : V} (hs : s ≠ t) (N : ℕ) :
    G.hitTime t N s - G.avg (G.hitTime t N) s ≤ 1 := by
  linarith [G.hitTime_le_succ t N s, G.hitTime_succ hs N]

/-- The truncated expected return time to `t`, defined by the first-step formula
`1 + avg (hitTime t N) t`; this equals `∑_{j ≤ N} Pr[the walk from t has not returned to t
within its first j steps]`. -/
def returnTime (t : V) (N : ℕ) : ℚ := 1 + G.avg (G.hitTime t N) t

/-- **Kac's bound.** The expected return time to a vertex of an `n`-vertex regular multigraph
is at most `n` [AB09, Exercise 7.11(c)] (the book asks for `≤ 10n`).

**Proof sketch.** Write `F = hitTime t N` and `ΔF = F − avg F`. Since the uniform distribution
is stationary, `∑ᵤ ΔF u = 0`. Every term with `u ≠ t` is at most `1`, so `−ΔF t =
avg F t ≤ n − 1`, as `F t = 0`. -/
theorem returnTime_le_card (t : V) (N : ℕ) : G.returnTime t N ≤ Fintype.card V := by
  set F := G.hitTime t N
  have hsum : ∑ u, (F u - G.avg F u) = 0 := by
    rw [Finset.sum_sub_distrib, G.sum_avg, sub_self]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)] at hsum
  have hrest : ∑ u ∈ univ.erase t, (F u - G.avg F u) ≤ ((univ.erase t).card : ℚ) := by
    calc ∑ u ∈ univ.erase t, (F u - G.avg F u) ≤ ∑ _u ∈ univ.erase t, (1 : ℚ) :=
          Finset.sum_le_sum fun u hu => G.hitTime_sub_avg_le (Finset.ne_of_mem_erase hu) N
      _ = _ := by simp
  have hcard : ((univ.erase t).card : ℚ) + 1 = Fintype.card V := by
    exact_mod_cast Finset.card_erase_add_one (Finset.mem_univ t)
  have hFt : F t = 0 := G.hitTime_self t N
  unfold returnTime
  linarith

/-- The walk's Dirichlet energy: `∑ᵤ ∑ᵢ (F u − F (nbr u i))² = 2·D·∑ᵤ F u·(F u − avg F u)`. -/
theorem sum_sq_eq_energy (F : V → ℚ) :
    ∑ u, ∑ i, (F u - F (G.nbr u i)) ^ 2 = 2 * D * ∑ u, F u * (F u - G.avg F u) := by
  have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  have hswap := G.sum_swap fun x y => F y * (F y - F x)
  have hsplit : ∑ u, ∑ i, (F u - F (G.nbr u i)) ^ 2 =
      ∑ u, ∑ i, F u * (F u - F (G.nbr u i)) +
        ∑ u, ∑ i, F (G.nbr u i) * (F (G.nbr u i) - F u) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, hswap, ← two_mul, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, avg]
  field_simp

omit [Fintype V] [NeZero D] in
/-- A path argument: if adjacent vertices differ in `F` by at most `a`, then `|F x − F t|` is at
most `a` times the length of any walk from `x` to `t` in the underlying simple graph. -/
private theorem abs_sub_le_length_mul {F : V → ℚ} {a : ℚ}
    (ha : ∀ x i, |F x - F (G.nbr x i)| ≤ a) {t : V} :
    ∀ {x : V} (p : (SimpleGraph.fromRel G.Adj).Walk x t), |F x - F t| ≤ p.length * a
  | _, .nil => by simp
  | x, .cons (v := y) h p => by
    have hxy : |F x - F y| ≤ a := by
      rcases ((SimpleGraph.fromRel_adj _ _ _).mp h).2 with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact ha x i
      · rw [abs_sub_comm]; exact ha y i
    have ih := abs_sub_le_length_mul ha p
    rw [SimpleGraph.Walk.length_cons]
    push_cast
    calc |F x - F t| = |(F x - F y) + (F y - F t)| := by ring_nf
      _ ≤ |F x - F y| + |F y - F t| := abs_add_le _ _
      _ ≤ a + p.length * a := add_le_add hxy ih
      _ = (p.length + 1) * a := by ring

omit [NeZero D] in
/-- A vertex connected to `t` is joined to it by a walk of length `< n` in the underlying simple
graph. -/
private theorem exists_short_walk {x t : V} (h : Relation.ReflTransGen G.Adj x t) :
    ∃ p : (SimpleGraph.fromRel G.Adj).Walk x t, p.length < Fintype.card V := by
  have hreach : (SimpleGraph.fromRel G.Adj).Reachable x t := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact SimpleGraph.Reachable.refl t
    | @head x' y' hxy _ ih =>
      by_cases hne : x' = y'
      · exact hne ▸ ih
      · exact (SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).mpr
          ⟨hne, Or.inl hxy⟩)).trans ih
  obtain ⟨p⟩ := hreach
  exact ⟨p.bypass, (p.bypass_isPath).length_lt⟩

/-- **Energy bound.** Let `F ≥ 0` vanish at `t`, satisfy `F u − avg F u ≤ 1` off `t`, and be
positive only on vertices connected to `t`. Then `F ≤ 2·D·n³` everywhere.

**Proof sketch.** Let `M = F s*` be the maximum and `a` the largest difference of `F` across an
edge slot. The energy identity gives `a² ≤ ∑ᵤ ∑ᵢ (F u − F(nbr u i))² ≤ 2·D·∑ᵤ F u ≤ 2·D·n·M`.
If `M > 0`, `s*` is joined to `t` by a walk of length `k < n`, so `M ≤ k·a` and
`M² ≤ k²·2·D·n·M`, whence `M ≤ 2·D·n·k² ≤ 2·D·n³`. -/
theorem le_of_energy (F : V → ℚ) (t : V) (hF0 : ∀ u, 0 ≤ F u) (hFt : F t = 0)
    (hsub : ∀ u, u ≠ t → F u - G.avg F u ≤ 1)
    (hconn : ∀ u, 0 < F u → Relation.ReflTransGen G.Adj u t) (u : V) :
    F u ≤ 2 * D * (Fintype.card V : ℚ) ^ 3 := by
  set n : ℚ := (Fintype.card V : ℚ)
  have hD0 : (0 : ℚ) ≤ D := Nat.cast_nonneg D
  haveI : Nonempty V := ⟨t⟩
  obtain ⟨s, hs⟩ := Finite.exists_max F
  set M := F s
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg _
  by_cases hM : M ≤ 0
  · exact (hs u).trans (hM.trans (by positivity))
  push_neg at hM
  -- energy bound: S ≤ 2·D·n·M
  set S := ∑ x, ∑ i, (F x - F (G.nbr x i)) ^ 2 with hSdef
  have hS : S ≤ 2 * D * (n * M) := by
    rw [hSdef, G.sum_sq_eq_energy]
    have h1 : ∑ x, F x * (F x - G.avg F x) ≤ ∑ x, F x := by
      refine Finset.sum_le_sum fun x _ => ?_
      by_cases hx : x = t
      · rw [hx, hFt]; simp
      · exact mul_le_of_le_one_right (hF0 x) (hsub x hx)
    have h2 : ∑ x, F x ≤ n * M := by
      calc ∑ x, F x ≤ ∑ _x : V, M := Finset.sum_le_sum fun x _ => hs x
        _ = n * M := by simp [n]
    have := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : (0 : ℚ) ≤ 2 * D)
    linarith
  -- the largest edge difference `a`, with `a² ≤ S`
  obtain ⟨⟨x₀, i₀⟩, hx₀⟩ := Finite.exists_max fun p : V × Fin D => |F p.1 - F (G.nbr p.1 p.2)|
  set a := |F x₀ - F (G.nbr x₀ i₀)|
  have ha : ∀ x i, |F x - F (G.nbr x i)| ≤ a := fun x i => hx₀ (x, i)
  have ha0 : 0 ≤ a := abs_nonneg _
  have haS : a ^ 2 ≤ S := by
    rw [sq_abs]
    calc (F x₀ - F (G.nbr x₀ i₀)) ^ 2 ≤ ∑ i, (F x₀ - F (G.nbr x₀ i)) ^ 2 :=
          Finset.single_le_sum (f := fun i => (F x₀ - F (G.nbr x₀ i)) ^ 2)
            (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
      _ ≤ S := Finset.single_le_sum (f := fun x => ∑ i, (F x - F (G.nbr x i)) ^ 2)
            (fun x _ => Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.mem_univ x₀)
  -- a short walk from `s` to `t`
  obtain ⟨p, hp⟩ := G.exists_short_walk (hconn s hM)
  set k : ℚ := (p.length : ℚ)
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hkn : k ≤ n := by simp only [k, n]; exact_mod_cast hp.le
  have hMk : M ≤ k * a := by
    have := G.abs_sub_le_length_mul ha p
    rw [hFt, sub_zero, abs_of_pos hM] at this
    exact this
  have hMM : M * M ≤ (k ^ 2 * (2 * D * n)) * M := by
    calc M * M ≤ (k * a) * (k * a) := mul_self_le_mul_self hM.le hMk
      _ = k ^ 2 * a ^ 2 := by ring
      _ ≤ k ^ 2 * S := mul_le_mul_of_nonneg_left haS (by positivity)
      _ ≤ k ^ 2 * (2 * D * (n * M)) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = (k ^ 2 * (2 * D * n)) * M := by ring
  have hM' : M ≤ k ^ 2 * (2 * D * n) := le_of_mul_le_mul_right hMM hM
  have hk2 : k ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hk0 hkn 2
  calc F u ≤ M := hs u
    _ ≤ k ^ 2 * (2 * D * n) := hM'
    _ ≤ n ^ 2 * (2 * D * n) := mul_le_mul_of_nonneg_right hk2 (by positivity)
    _ = 2 * D * n ^ 3 := by ring

/-- **Hitting time.** If `s` is connected to `t`, the expected time for the walk from `s` to
reach `t` is at most `2·D·n³`: `hitTime t N s ≤ 2·D·n³` for every truncation `N`; the
route to [AB09, §7.7, p.139].

**Proof sketch.** Apply `le_of_energy` to `F = hitTime t N` restricted to the connected
component of `t` (zero elsewhere). The component is closed under taking neighbours, so on it
`F − avg F ≤ 1` is first-step analysis (`hitTime_sub_avg_le`); off it `F = 0 ≤ avg F`. -/
theorem hitTime_le {s t : V} (hst : Relation.ReflTransGen G.Adj s t) (N : ℕ) :
    G.hitTime t N s ≤ 2 * D * (Fintype.card V : ℚ) ^ 3 := by
  classical
  let C : V → Prop := fun u => Relation.ReflTransGen G.Adj u t
  let F : V → ℚ := fun u => if C u then G.hitTime t N u else 0
  have hF0 : ∀ u, 0 ≤ F u := fun u => by
    simp only [F]; split_ifs
    · exact G.hitTime_nonneg t N u
    · exact le_rfl
  have hclosed : ∀ u i, C u → C (G.nbr u i) := fun u i hu =>
    Relation.ReflTransGen.head (G.adj_symm ⟨i, rfl⟩) hu
  have hsub : ∀ u, u ≠ t → F u - G.avg F u ≤ 1 := by
    intro u hu
    by_cases hC : C u
    · have havg : G.avg F u = G.avg (G.hitTime t N) u := by
        unfold avg
        congr 1
        exact Finset.sum_congr rfl fun i _ => if_pos (hclosed u i hC)
      simp only [F, if_pos hC]
      rw [havg]
      exact G.hitTime_sub_avg_le hu N
    · have : 0 ≤ G.avg F u := by
        unfold avg
        exact div_nonneg (Finset.sum_nonneg fun i _ => hF0 _) (Nat.cast_nonneg D)
      simp only [F, if_neg hC]
      linarith
  have hFt : F t = 0 := by simp only [F]; split_ifs <;> simp [G.hitTime_self]
  have hconn : ∀ u, 0 < F u → C u := fun u hu => by
    by_contra hC
    simp only [F, if_neg hC] at hu
    exact lt_irrefl _ hu
  have := G.le_of_energy F t hF0 hFt hsub hconn s
  simp only [F] at this
  rwa [if_pos (show C s from hst)] at this

/-- **Markov's inequality** for the hitting time: `(L+1)·Pr[the L-step walk avoids t] ≤
hitTime t (L+1) s`. -/
theorem succ_mul_missProb_le (t : V) (L : ℕ) (s : V) :
    (L + 1 : ℚ) * G.missProb t L s ≤ G.hitTime t (L + 1) s := by
  unfold hitTime
  calc (L + 1 : ℚ) * G.missProb t L s = ∑ _j ∈ range (L + 1), G.missProb t L s := by simp
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
        G.missProb_antitone t s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

/-- A walk of length `L` from `s` visits a connected `t` with probability at least
`1 − 2·D·n³/(L+1)` [AB09, §7.7, p.139]. -/
theorem one_sub_le_hitProb {s t : V} (hst : Relation.ReflTransGen G.Adj s t) (L : ℕ) :
    1 - 2 * D * (Fintype.card V : ℚ) ^ 3 / (L + 1) ≤ G.hitProb t L s := by
  have h := (G.succ_mul_missProb_le t L s).trans (G.hitTime_le hst (L + 1))
  have hL : (0 : ℚ) < L + 1 := by positivity
  rw [sub_le_comm, le_div_iff₀ hL]
  have : G.missProb t L s = 1 - G.hitProb t L s := rfl
  rw [this, mul_comm] at h
  exact h

/-- **Expected hitting time `≤ 10n⁴`.** With degree `D ≤ 2n`, the walk from `s` reaches a
connected `t` in expected time at most `10n⁴` [AB09, §7.7, p.139]. -/
theorem hitTime_le_ten_mul_pow_four (hD : D ≤ 2 * Fintype.card V) {s t : V}
    (hst : Relation.ReflTransGen G.Adj s t) (N : ℕ) :
    G.hitTime t N s ≤ 10 * (Fintype.card V : ℚ) ^ 4 := by
  have hD' : (D : ℚ) ≤ 2 * Fintype.card V := by exact_mod_cast hD
  have hn : (0 : ℚ) ≤ (Fintype.card V : ℚ) ^ 3 := by positivity
  have hn1 : (0 : ℚ) ≤ (Fintype.card V : ℚ) := Nat.cast_nonneg _
  calc G.hitTime t N s ≤ 2 * D * (Fintype.card V : ℚ) ^ 3 := G.hitTime_le hst N
    _ ≤ 2 * (2 * Fintype.card V) * (Fintype.card V : ℚ) ^ 3 := by gcongr
    _ ≤ 10 * (Fintype.card V : ℚ) ^ 4 := by nlinarith [hn, hn1]

/-- **[AB09, Theorem 7.19], probabilistic core.** On an `n`-vertex `D`-regular multigraph with
`D ≤ 2n`, a random walk of length `100n⁴` from `s` visits any `t` connected to `s` with
probability at least `3/4`. -/
theorem three_quarters_le_hitProb (hD : D ≤ 2 * Fintype.card V) {s t : V}
    (hst : Relation.ReflTransGen G.Adj s t) :
    3 / 4 ≤ G.hitProb t (100 * Fintype.card V ^ 4) s := by
  have h := G.one_sub_le_hitProb hst (100 * Fintype.card V ^ 4)
  have hD' : (D : ℚ) ≤ 2 * Fintype.card V := by exact_mod_cast hD
  set n : ℚ := (Fintype.card V : ℚ)
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg _
  push_cast at h
  have hL : (0 : ℚ) < 100 * n ^ 4 + 1 := by positivity
  have hfrac : 2 * D * n ^ 3 / (100 * n ^ 4 + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ hL]
    have : 2 * D * n ^ 3 ≤ 4 * n ^ 4 := by
      have := mul_le_mul_of_nonneg_right hD' (by positivity : (0 : ℚ) ≤ 2 * n ^ 3)
      nlinarith
    nlinarith [pow_nonneg hn 4]
  linarith

/-! ### [AB09, Exercise 7.11(d)] as printed: `E_{u,v} ≤ 100kn²` -/

omit [Fintype V] in
/-- A truncated hitting time is at most its truncation: `hitTime t N s ≤ N`. -/
theorem hitTime_le_trunc (t : V) (N : ℕ) (s : V) : G.hitTime t N s ≤ N := by
  unfold hitTime
  calc ∑ j ∈ range N, G.missProb t j s ≤ ∑ _j ∈ range N, (1 : ℚ) :=
        Finset.sum_le_sum fun j _ => (G.missProb_mem_Icc t j s).2
    _ = N := by simp

/-- **One edge.** If `u` is adjacent to `v`, the walk from `u` reaches `v` in expected time at
most `D·(n − 1)`: a slot of `v` leads to `u`, so `E_{u,v}/D ≤ E_v⁺ − 1 ≤ n − 1`. -/
theorem hitTime_le_of_adj {u v : V} (h : G.Adj u v) (N : ℕ) :
    G.hitTime v N u ≤ D * ((Fintype.card V : ℚ) - 1) := by
  obtain ⟨i, hi⟩ := G.adj_symm h
  have hD : (0 : ℚ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
  have hsum : G.hitTime v N u ≤ ∑ j, G.hitTime v N (G.nbr v j) := by
    rw [← hi]
    exact Finset.single_le_sum (f := fun j => G.hitTime v N (G.nbr v j))
      (fun j _ => G.hitTime_nonneg v N _) (Finset.mem_univ i)
  have hret := G.returnTime_le_card v N
  unfold returnTime avg at hret
  have h1 : (∑ j, G.hitTime v N (G.nbr v j)) / D ≤ (Fintype.card V : ℚ) - 1 := by linarith
  rw [div_le_iff₀ hD] at h1
  linarith

/-- **First passage through `b`.** For every `M`, `E_{x,c} − E_{b,c} ≤ E^{(M)}_{x,b} +
N·Pr[τ_b > M from x]`, where `E_{·,c}` is truncated at `N`.

**Proof sketch.** Induct on `M`. At `M = 0` the left side is at most `N` (`hitTime_le_trunc`)
unless `x = b`. In the step, the cases `x = b` and `x = c` are immediate; otherwise first-step
analysis (`hitTime_succ`, `missProb_succ`) turns both sides into neighbour averages, and
`hitTime_sub_avg_le` together with the induction hypothesis under `avg_mono` closes it. -/
theorem hitTime_sub_le (c b : V) (N M : ℕ) (x : V) :
    G.hitTime c N x - G.hitTime c N b ≤ G.hitTime b M x + N * G.missProb b M x := by
  induction M generalizing x with
  | zero =>
    by_cases hx : x = b
    · subst hx; rw [sub_self, G.missProb_self]; simp [hitTime]
    · rw [G.missProb_zero_of_ne hx]
      have : G.hitTime b 0 x = 0 := by simp [hitTime]
      linarith [G.hitTime_le_trunc c N x, G.hitTime_nonneg c N b]
  | succ M ih =>
    have hR : 0 ≤ G.hitTime b (M + 1) x + N * G.missProb b (M + 1) x :=
      add_nonneg (G.hitTime_nonneg _ _ _)
        (mul_nonneg (Nat.cast_nonneg N) (G.missProb_mem_Icc _ _ _).1)
    by_cases hxb : x = b
    · subst hxb; rw [sub_self]; exact hR
    by_cases hxc : x = c
    · subst hxc; rw [G.hitTime_self]; linarith [G.hitTime_nonneg x N b]
    have h1 := G.hitTime_sub_avg_le hxc N
    have h2 := G.avg_mono ih x
    have e1 : G.avg (fun y => G.hitTime c N y - G.hitTime c N b) x =
        G.avg (G.hitTime c N) x - G.hitTime c N b := by
      have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
      unfold avg
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    have e2 : G.avg (fun y => G.hitTime b M y + N * G.missProb b M y) x =
        G.avg (G.hitTime b M) x + N * G.avg (G.missProb b M) x := by
      unfold avg; rw [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    rw [G.hitTime_succ hxb, missProb_succ, if_neg hxb]
    linarith

/-- **Triangle inequality for hitting times.** If the walk from `a` reaches `b` in expected time
at most `A`, then `E_{a,c} ≤ A + E_{b,c}`.

**Proof sketch.** Put `ε = E_{a,c} − A − E_{b,c}`. By `hitTime_sub_le`,
`ε ≤ N·Pr[τ_b > M]`, and by Markov (`succ_mul_missProb_le`) `(M+1)·Pr[τ_b > M] ≤ A`; so
`(M+1)·ε ≤ N·A` for every `M`, forcing `ε ≤ 0`. -/
theorem hitTime_le_add {a b c : V} {A : ℚ} (hA : ∀ M, G.hitTime b M a ≤ A) (N : ℕ) :
    G.hitTime c N a ≤ A + G.hitTime c N b := by
  by_contra hlt
  push_neg at hlt
  set ε := G.hitTime c N a - A - G.hitTime c N b with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have hM : ∀ M : ℕ, ((M : ℚ) + 1) * ε ≤ N * A := by
    intro M
    have h1 := G.hitTime_sub_le c b N M a
    have h2 := (G.succ_mul_missProb_le b M a).trans (hA (M + 1))
    have h3 : ε ≤ N * G.missProb b M a := by rw [hεdef]; linarith [hA M]
    calc ((M : ℚ) + 1) * ε ≤ (M + 1) * (N * G.missProb b M a) := by gcongr
      _ = N * ((M + 1) * G.missProb b M a) := by ring
      _ ≤ N * A := by gcongr
  obtain ⟨M, hM'⟩ := exists_nat_gt (N * A / ε)
  rw [div_lt_iff₀ hε] at hM'
  linarith [hM M]

/-- **Along a path.** If `u` is joined to `v` by a walk of length `k` in the underlying simple
graph, the walk from `u` reaches `v` in expected time at most `k·D·(n − 1)`. -/
theorem hitTime_le_length_mul {v : V} :
    ∀ {u : V} (p : (SimpleGraph.fromRel G.Adj).Walk u v) (N : ℕ),
      G.hitTime v N u ≤ p.length * (D * ((Fintype.card V : ℚ) - 1))
  | _, .nil, N => by rw [G.hitTime_self]; simp
  | u, .cons (v := y) h p, N => by
    have huy : G.Adj u y := by
      rcases ((SimpleGraph.fromRel_adj _ _ _).mp h).2 with h' | h'
      · exact h'
      · exact G.adj_symm h'
    have ih := hitTime_le_length_mul p N
    have htri := G.hitTime_le_add (c := v) (fun M => G.hitTime_le_of_adj huy M) N
    rw [SimpleGraph.Walk.length_cons]
    push_cast
    linarith

/-- **[AB09, Exercise 7.11(d)].** If `u` and `v` are joined by a path of length at most `k` and
`D ≤ 100n`, then `E_{u,v} ≤ 100kn²`: `hitTime v N u ≤ 100·k·n²` for every truncation `N`. -/
theorem hitTime_le_hundred_mul (hD : D ≤ 100 * Fintype.card V) {u v : V} {k : ℕ}
    (p : (SimpleGraph.fromRel G.Adj).Walk u v) (hk : p.length ≤ k) (N : ℕ) :
    G.hitTime v N u ≤ 100 * k * (Fintype.card V : ℚ) ^ 2 := by
  haveI : Nonempty V := ⟨u⟩
  have hn : (1 : ℚ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD' : (D : ℚ) ≤ 100 * Fintype.card V := by exact_mod_cast hD
  have hk' : (p.length : ℚ) ≤ k := by exact_mod_cast hk
  set n : ℚ := (Fintype.card V : ℚ)
  have hn1 : 0 ≤ n - 1 := by linarith
  have hDn : (D : ℚ) * (n - 1) ≤ 100 * n ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hD' hn1]
  calc G.hitTime v N u ≤ p.length * (D * (n - 1)) := G.hitTime_le_length_mul p N
    _ ≤ k * (100 * n ^ 2) :=
        mul_le_mul hk' hDn (mul_nonneg (Nat.cast_nonneg D) hn1) (Nat.cast_nonneg k)
    _ = 100 * k * n ^ 2 := by ring

/-- **[AB09, Exercise 7.11(d)], conclusion.** If `D ≤ 100n` and `s` is connected to `t`, a
random walk of length `1000n³` from `s` misses `t` with probability at most `1/10`. -/
theorem missProb_thousand_mul_pow_three_le (hD : D ≤ 100 * Fintype.card V) {s t : V}
    (hst : Relation.ReflTransGen G.Adj s t) :
    G.missProb t (1000 * Fintype.card V ^ 3) s ≤ 1 / 10 := by
  obtain ⟨p, hp⟩ := G.exists_short_walk hst
  have h := (G.succ_mul_missProb_le t (1000 * Fintype.card V ^ 3) s).trans
    (G.hitTime_le_hundred_mul hD p hp.le _)
  push_cast at h
  set n : ℚ := (Fintype.card V : ℚ)
  set m := G.missProb t (1000 * Fintype.card V ^ 3) s
  by_contra hlt
  push_neg at hlt
  have : (1000 * n ^ 3 + 1) * (1 / 10) < (1000 * n ^ 3 + 1) * m :=
    mul_lt_mul_of_pos_left hlt (by positivity)
  linarith

end RegularMultigraph

end Randomized
