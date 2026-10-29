/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.RandomWalkCover
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Fintype.Lattice

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Convergence of random walks to the uniform distribution

[AB09, Exercise 7.11(b)] (p.142): on a connected, non-bipartite, regular graph `G` with `n`
vertices, the distance `Δ(p) = maxᵢ (pᵢ − 1/n)` of a distribution from uniform contracts by a
factor `1 − n^{−10n}` after some fixed number of walk steps; hence the uniform distribution is
the only stationary one, and a long walk from `u` visits `v` about `N/n` times.

## Main definitions

* `Randomized.RegularMultigraph.transProb` — the `k`-step transition probability.
* `Randomized.RegularMultigraph.walkDist` — the distribution `p^k`.
* `Randomized.RegularMultigraph.IsStationary` — `p^1 = p`.
* `Randomized.uniformExcess` — `Δ(p) = maxᵢ (pᵢ − 1/n)`.
* `Randomized.RegularMultigraph.visits`, `expVisits` — the number of visits to `v` along a
  walk and its expectation over a uniform `N`-step walk.

## Main results

* `Randomized.RegularMultigraph.exists_uniformExcess_walkDist_le` — the contraction
  `Δ(p^k) ≤ (1 − n^{−10n})·Δ(p)` [AB09, Exercise 7.11(b)];
  `Randomized.RegularMultigraph.uniformExcess_walkDist_two_mul_le` — `k = 2n` when `D ≤ n⁵`.
* `Randomized.RegularMultigraph.isStationary_iff_eq_uniform` — the uniform distribution is the
  only stationary distribution [AB09, Exercise 7.11(b)(a)]; for real-valued `p`,
  `Randomized.RegularMultigraph.isStationary_real_iff_eq_uniform`.
* `Randomized.RegularMultigraph.exists_le_expVisits` — for all large `N`, an `N`-step walk
  from `u` visits `v` at least `N/(2n)` times in expectation [AB09, Exercise 7.11(b)(b)].

## Divergences

* `G` is a `D`-regular multigraph (`Randomized.RegularMultigraph`), parallel edges and loops
  allowed; "non-bipartite" is `¬ IsBipartite` (`TCSlib.Complexity.Randomized.RandomWalkCover`).
* The `k` of the contraction depends only on `G`, not on `p`. In general it is not bounded in
  terms of `n` (heavy parallel edges slow mixing); in the book's setting of a simple graph
  (`D ≤ n`, indeed any `D ≤ n⁵`) it is `2n`. The contraction and uniqueness
  statements assume only `∑ᵢ pᵢ = 1`, so they hold for every distribution. Visits are counted
  at positions `1, …, N` of the walk.
* Distributions are `ℚ`-valued (the house style of exact rational probabilities); uniqueness
  of the stationary distribution is also proved for `ℝ`-valued `p`
  (`isStationary_real_iff_eq_uniform`, stationarity stated pointwise).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset

/-- `Δ(p) = maxᵢ (pᵢ − 1/n)`: the largest excess of `p` over the uniform distribution
[AB09, Exercise 7.11(b)]. -/
def uniformExcess {V : Type*} [Fintype V] [Nonempty V] (p : V → ℚ) : ℚ :=
  univ.sup' univ_nonempty fun i => p i - 1 / Fintype.card V

section Excess

variable {V : Type*} [Fintype V] [Nonempty V]

/-- Every coordinate's excess is at most `Δ(p)`. -/
theorem le_uniformExcess (p : V → ℚ) (i : V) : p i - 1 / Fintype.card V ≤ uniformExcess p :=
  Finset.le_sup' (fun i => p i - 1 / Fintype.card V) (mem_univ i)

/-- The excesses of a mass-one `p` sum to zero. -/
theorem sum_sub_inv_card {p : V → ℚ} (hp : ∑ v, p v = 1) :
    ∑ v, (p v - 1 / Fintype.card V) = 0 := by
  have hn : (Fintype.card V : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.sum_sub_distrib, hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one_div_cancel hn, sub_self]

/-- `Δ(p) ≥ 0` for every `p` of total mass one. -/
theorem uniformExcess_nonneg {p : V → ℚ} (hp : ∑ v, p v = 1) : 0 ≤ uniformExcess p := by
  have hn : (0 : ℚ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have h : (0 : ℚ) ≤ Fintype.card V * uniformExcess p := by
    calc (0 : ℚ) = ∑ v, (p v - 1 / Fintype.card V) := (sum_sub_inv_card hp).symm
      _ ≤ ∑ _v : V, uniformExcess p := Finset.sum_le_sum fun v _ => le_uniformExcess p v
      _ = Fintype.card V * uniformExcess p := by simp
  exact nonneg_of_mul_nonneg_right (by linarith) hn

/-- A lower bound from `Δ`: every coordinate of a mass-one `p` is at least `1/n − n·Δ(p)`. -/
theorem inv_card_sub_le {p : V → ℚ} (hp : ∑ v, p v = 1) (v : V) :
    1 / Fintype.card V - Fintype.card V * uniformExcess p ≤ p v := by
  classical
  have h0 := uniformExcess_nonneg hp
  have h := sum_sub_inv_card hp
  rw [← Finset.add_sum_erase _ _ (mem_univ v)] at h
  have hle : ∑ w ∈ univ.erase v, (p w - 1 / Fintype.card V) ≤
      Fintype.card V * uniformExcess p :=
    calc ∑ w ∈ univ.erase v, (p w - 1 / Fintype.card V)
        ≤ ∑ _w ∈ univ.erase v, uniformExcess p :=
          Finset.sum_le_sum fun w _ => le_uniformExcess p w
      _ ≤ ∑ _w : V, uniformExcess p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => h0
      _ = Fintype.card V * uniformExcess p := by simp
  linarith

/-- **Contraction from a minorant.** If `P` has column sums `1` and entries `≥ δ`, one
application of `P` to a mass-one `p` shrinks `Δ` by the factor `1 − n·δ`. -/
theorem uniformExcess_le_of_minorant (P : V → V → ℚ) (hcol : ∀ v, ∑ u, P u v = 1) {δ : ℚ}
    (hδ : ∀ u v, δ ≤ P u v) {p : V → ℚ} (hp : ∑ v, p v = 1) :
    uniformExcess (fun v => ∑ u, p u * P u v) ≤
      (1 - Fintype.card V * δ) * uniformExcess p := by
  refine Finset.sup'_le _ _ fun v _ => ?_
  set n : ℚ := (Fintype.card V : ℚ)
  have h1 := sum_sub_inv_card hp
  calc ∑ u, p u * P u v - 1 / n
      = ∑ u, ((p u - 1 / n) * (P u v - δ) + 1 / n * P u v + δ * (p u - 1 / n)) - 1 / n := by
        congr 1; exact Finset.sum_congr rfl fun u _ => by ring
    _ = ∑ u, (p u - 1 / n) * (P u v - δ) + 1 / n * ∑ u, P u v
          + δ * ∑ u, (p u - 1 / n) - 1 / n := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = ∑ u, (p u - 1 / n) * (P u v - δ) := by rw [hcol, h1]; ring
    _ ≤ ∑ u, uniformExcess p * (P u v - δ) := Finset.sum_le_sum fun u _ =>
        mul_le_mul_of_nonneg_right (le_uniformExcess p u) (sub_nonneg.mpr (hδ u v))
    _ = (1 - n * δ) * uniformExcess p := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, hcol]; simp [n]; ring

end Excess

namespace RegularMultigraph

variable {V : Type*} [DecidableEq V] {D : ℕ} (G : RegularMultigraph V D)

/-- The `k`-step transition probability `Pr[the k-step walk from u ends at v]`. -/
def transProb (k : ℕ) (u v : V) : ℚ := idxProb D k fun w => G.endpoint u w = v

/-- In zero steps the walk stays put. -/
theorem transProb_zero (u v : V) : G.transProb 0 u v = if u = v then 1 else 0 := by
  unfold transProb; rw [idxProb_zero]; rfl

/-- First-step recursion: `P^{k+1}(u, v)` averages `P^k(·, v)` over the neighbours of `u`. -/
theorem transProb_succ [NeZero D] (k : ℕ) (u v : V) :
    G.transProb (k + 1) u v = G.avg (fun x => G.transProb k x v) u := by
  unfold transProb avg
  rw [idxProb_succ]
  rfl

/-- One step moves from `u` to `v` with probability `mult u v / D`. -/
theorem transProb_one [NeZero D] (u v : V) : G.transProb 1 u v = G.mult u v / D := by
  rw [transProb_succ, avg]
  simp only [transProb_zero]
  rw [Finset.sum_boole]
  rfl

/-- Transition probabilities are nonnegative. -/
theorem transProb_nonneg (k : ℕ) (u v : V) : 0 ≤ G.transProb k u v := by
  unfold transProb idxProb; positivity

/-- A walk word of length `k` from `u` to `v` gives `P^k(u, v) ≥ D^{−k}`. -/
theorem one_div_pow_le_transProb [NeZero D] {u v : V} (w : List (Fin D))
    (h : G.endpoint u w = v) : 1 / (D : ℚ) ^ w.length ≤ G.transProb w.length u v := by
  unfold transProb idxProb
  have hpos : 0 < (univ.filter fun x : Fin w.length → Fin D =>
      G.endpoint u (List.ofFn x) = v).card :=
    Finset.card_pos.mpr ⟨w.get, by simp [List.ofFn_get, h]⟩
  gcongr
  exact_mod_cast hpos

/-- The number of visits to `v` at positions `1, …, |w|` of the walk from `u` along `w`. -/
def visits (v : V) : V → List (Fin D) → ℕ
  | _, [] => 0
  | u, i :: w => (if G.nbr u i = v then 1 else 0) + visits v (G.nbr u i) w

/-- The expected number of visits to `v` by a uniformly random `N`-step walk from `u`. -/
def expVisits (v : V) (N : ℕ) (u : V) : ℚ :=
  (∑ w : Fin N → Fin D, (G.visits v u (List.ofFn w) : ℚ)) / (D : ℚ) ^ N

/-- Conditioning the expected visit count on the first step. -/
theorem expVisits_succ [NeZero D] (v : V) (N : ℕ) (u : V) :
    G.expVisits v (N + 1) u =
      (∑ i, ((if G.nbr u i = v then 1 else 0) + G.expVisits v N (G.nbr u i))) / D := by
  have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  have hDN : (D : ℚ) ^ N ≠ 0 := pow_ne_zero _ hD
  have h : ∀ (i : Fin D) (w : Fin N → Fin D),
      (G.visits v u (List.ofFn ((Fin.consEquiv fun _ => Fin D) (i, w))) : ℚ) =
        (if G.nbr u i = v then 1 else 0) + G.visits v (G.nbr u i) (List.ofFn w) := by
    intro i w
    simp [Fin.consEquiv, List.ofFn_succ, visits]
  unfold expVisits
  rw [← (Fin.consEquiv fun _ => Fin D).sum_comp, Fintype.sum_prod_type]
  simp only [h]
  rw [Finset.sum_div, Finset.sum_div, pow_succ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  simp only [Fintype.card_fin]
  ring

/-- Linearity of expectation: the expected visit count is `∑_{j=1}^{N} P^j(u, v)`. -/
theorem expVisits_eq [NeZero D] (v : V) (N : ℕ) (u : V) :
    G.expVisits v N u = ∑ j ∈ range N, G.transProb (j + 1) u v := by
  induction N generalizing u with
  | zero => simp [expVisits, visits]
  | succ N ih =>
    rw [expVisits_succ, Finset.sum_range_succ']
    simp only [ih]
    rw [Finset.sum_add_distrib, add_div, add_comm]
    congr 1
    · rw [Finset.sum_comm, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [G.transProb_succ (j + 1), avg, Finset.sum_div]
    · rw [G.transProb_succ 0, avg]
      simp only [transProb_zero]

variable [Fintype V]

/-- Each row of `P^k` sums to one. -/
theorem sum_transProb_right [NeZero D] (k : ℕ) (u : V) : ∑ v, G.transProb k u v = 1 := by
  have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  induction k generalizing u with
  | zero => simp [transProb_zero]
  | succ k ih =>
    simp only [transProb_succ, avg]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp [ih, hD]

/-- Each column of `P^k` sums to one: the walk is doubly stochastic. -/
theorem sum_transProb_left [NeZero D] (k : ℕ) (v : V) : ∑ u, G.transProb k u v = 1 := by
  induction k with
  | zero => simp [transProb_zero]
  | succ k ih =>
    simp only [transProb_succ]
    rw [G.sum_avg]
    exact ih

/-- Chapman–Kolmogorov: `P^{k+1}(u, v) = ∑ₓ P(u, x)·P^k(x, v)`. -/
theorem transProb_succ_eq_sum [NeZero D] (k : ℕ) (u v : V) :
    G.transProb (k + 1) u v = ∑ x, G.transProb 1 u x * G.transProb k x v := by
  rw [transProb_succ, avg, G.sum_nbr_eq u (fun x => G.transProb k x v), Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [transProb_one]
  ring

/-- The distribution `p^k` of the walk after `k` steps from a start drawn from `p`
[AB09, Exercise 7.11(b)]. -/
def walkDist (p : V → ℚ) (k : ℕ) (v : V) : ℚ := ∑ u, p u * G.transProb k u v

/-- `p^0 = p`. -/
theorem walkDist_zero (p : V → ℚ) : G.walkDist p 0 = p := by
  funext v; simp [walkDist, transProb_zero]

/-- `p^{k+1} = (p^1)^k`. -/
theorem walkDist_succ [NeZero D] (p : V → ℚ) (k : ℕ) :
    G.walkDist p (k + 1) = G.walkDist (G.walkDist p 1) k := by
  funext v
  have h := fun u => G.transProb_succ_eq_sum k u v
  simp only [walkDist, h, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => by ring

/-- The semigroup law `p^{a+b} = (p^a)^b`. -/
theorem walkDist_add [NeZero D] (p : V → ℚ) (a b : ℕ) :
    G.walkDist p (a + b) = G.walkDist (G.walkDist p a) b := by
  induction a generalizing p with
  | zero => rw [zero_add, walkDist_zero]
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by ring, walkDist_succ, ih, ← walkDist_succ]

/-- The walk preserves total mass. -/
theorem sum_walkDist [NeZero D] (p : V → ℚ) (k : ℕ) : ∑ v, G.walkDist p k v = ∑ v, p v := by
  simp only [walkDist]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, sum_transProb_right]

/-- `p` is stationary: drawing a vertex from `p` and taking one random step yields `p`
[AB09, Exercise 7.11(a)]. -/
def IsStationary (p : V → ℚ) : Prop := G.walkDist p 1 = p

/-- The uniform distribution is stationary [AB09, Exercise 7.11(a)]. -/
theorem uniform_isStationary [NeZero D] :
    G.IsStationary fun _ => 1 / (Fintype.card V : ℚ) := by
  funext v; simp only [walkDist, transProb_one]
  exact G.uniform_stationary v

/-- On a connected non-bipartite `G`, every `2n`-step transition probability is at least
`D^{−2n}`. -/
theorem one_div_pow_le_transProb_two_mul [NeZero D] (hc : G.Connected) (hb : ¬ G.IsBipartite)
    (u v : V) :
    1 / (D : ℚ) ^ (2 * Fintype.card V) ≤ G.transProb (2 * Fintype.card V) u v := by
  obtain ⟨w, hl, he⟩ := G.exists_endpoint_eq_two_mul hc hb u v
  have := G.one_div_pow_le_transProb w he
  rwa [hl] at this

variable [NeZero D] [Nonempty V]

/-- Walking never increases `Δ` of a mass-one `p`. -/
theorem uniformExcess_walkDist_le_self {p : V → ℚ} (hp : ∑ v, p v = 1) (k : ℕ) :
    uniformExcess (G.walkDist p k) ≤ uniformExcess p := by
  have := uniformExcess_le_of_minorant (G.transProb k) (G.sum_transProb_left k)
    (fun u v => G.transProb_nonneg k u v) hp
  simpa using this

/-- Iterating a contraction: if `K` steps shrink `Δ` by `c ≥ 0`, then `i·K` steps shrink it
by `cⁱ`. -/
theorem uniformExcess_walkDist_mul_le {K : ℕ} {c : ℚ} (hc0 : 0 ≤ c)
    (hK : ∀ p : V → ℚ, ∑ v, p v = 1 → uniformExcess (G.walkDist p K) ≤ c * uniformExcess p)
    (i : ℕ) {p : V → ℚ} (hp : ∑ v, p v = 1) :
    uniformExcess (G.walkDist p (i * K)) ≤ c ^ i * uniformExcess p := by
  induction i with
  | zero => simp [walkDist_zero]
  | succ i ih =>
    rw [show (i + 1) * K = i * K + K by ring, walkDist_add, pow_succ]
    calc uniformExcess (G.walkDist (G.walkDist p (i * K)) K)
        ≤ c * uniformExcess (G.walkDist p (i * K)) := hK _ (by rw [sum_walkDist, hp])
      _ ≤ c * (c ^ i * uniformExcess p) := mul_le_mul_of_nonneg_left ih hc0
      _ = c ^ i * c * uniformExcess p := by ring

/-- Every `2n` steps shrink `Δ` by `1 − n·D^{−2n} ≥ 0`: every entry of `P^{2n}` is `≥ D^{−2n}`
and its columns sum to `1`. -/
private theorem uniformExcess_walkDist_two_mul_le_aux (hc : G.Connected)
    (hb : ¬ G.IsBipartite) :
    (Fintype.card V : ℚ) * (1 / (D : ℚ) ^ (2 * Fintype.card V)) ≤ 1 ∧
      ∀ p : V → ℚ, ∑ v, p v = 1 → uniformExcess (G.walkDist p (2 * Fintype.card V)) ≤
        (1 - Fintype.card V * (1 / (D : ℚ) ^ (2 * Fintype.card V))) * uniformExcess p := by
  have hδ := G.one_div_pow_le_transProb_two_mul hc hb
  refine ⟨?_, fun p hp => uniformExcess_le_of_minorant _ (G.sum_transProb_left _) hδ hp⟩
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  calc (Fintype.card V : ℚ) * (1 / (D : ℚ) ^ (2 * Fintype.card V))
      = ∑ _u : V, 1 / (D : ℚ) ^ (2 * Fintype.card V) := by simp
    _ ≤ ∑ u, G.transProb (2 * Fintype.card V) u v := Finset.sum_le_sum fun u _ => hδ u v
    _ = 1 := G.sum_transProb_left _ v

/-- **[AB09, Exercise 7.11(b)].** On a connected non-bipartite `D`-regular multigraph there is
`k` with `Δ(p^k) ≤ (1 − n^{−10n})·Δ(p)` for every distribution `p`; for `D ≤ n⁵`, `k = 2n`
(`uniformExcess_walkDist_two_mul_le`).

**Proof sketch.** By `uniformExcess_walkDist_two_mul_le_aux`, `2n` steps contract `Δ` by
`c = 1 − n·D^{−2n} ∈ [0, 1)`. For `n ≥ 2` take `m` with `cᵐ < 1 − n^{−10n}` and `k = 2nm`;
for `n = 1`, `Δ(p) = 0`. -/
theorem exists_uniformExcess_walkDist_le (hc : G.Connected) (hb : ¬ G.IsBipartite) :
    ∃ k, ∀ p : V → ℚ, ∑ v, p v = 1 →
      uniformExcess (G.walkDist p k) ≤
        (1 - 1 / (Fintype.card V : ℚ) ^ (10 * Fintype.card V)) * uniformExcess p := by
  obtain ⟨hnδ, hK⟩ := G.uniformExcess_walkDist_two_mul_le_aux hc hb
  set n := Fintype.card V
  set δ : ℚ := 1 / (D : ℚ) ^ (2 * n)
  have hδ0 : 0 < δ := by
    have : (0 : ℚ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
    positivity
  rcases eq_or_lt_of_le (show 1 ≤ n from Fintype.card_pos) with h1 | h2
  · refine ⟨0, fun p hp => ?_⟩
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp h1.symm
    have hpx : p x = 1 := by
      rw [← hp, Finset.sum_eq_single x (fun y _ hy => absurd (hx y) hy) (by simp)]
    have hcard : Fintype.card V = 1 := h1.symm
    have h0 : uniformExcess p ≤ 0 := Finset.sup'_le _ _ fun y _ => by
      rw [hx y, hpx, hcard]; norm_num
    have hn1 : (n : ℚ) = 1 := by exact_mod_cast h1.symm
    rw [walkDist_zero, hn1]
    norm_num
    exact h0
  · have hn2 : (1 : ℚ) < n := by exact_mod_cast h2
    have ht : 0 < 1 - 1 / (n : ℚ) ^ (10 * n) := by
      have : 1 / (n : ℚ) ^ (10 * n) < 1 := by
        rw [div_lt_one (by positivity)]; exact one_lt_pow₀ hn2 (by omega)
      linarith
    have hc1 : 1 - n * δ < 1 := by
      have : 0 < (n : ℚ) * δ := mul_pos (by linarith) hδ0
      linarith
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one ht hc1
    refine ⟨m * (2 * n), fun p hp => ?_⟩
    exact (G.uniformExcess_walkDist_mul_le (by linarith) hK m hp).trans
      (mul_le_mul_of_nonneg_right hm.le (uniformExcess_nonneg hp))

/-- **[AB09, Exercise 7.11(b)], the book's constant at `k = 2n`.** If moreover `D ≤ n⁵` (e.g. a
simple graph, `D ≤ n`), then `Δ(p^{2n}) ≤ (1 − n^{−10n})·Δ(p)`. -/
theorem uniformExcess_walkDist_two_mul_le (hc : G.Connected) (hb : ¬ G.IsBipartite)
    (hD : D ≤ Fintype.card V ^ 5) {p : V → ℚ} (hp : ∑ v, p v = 1) :
    uniformExcess (G.walkDist p (2 * Fintype.card V)) ≤
      (1 - 1 / (Fintype.card V : ℚ) ^ (10 * Fintype.card V)) * uniformExcess p := by
  refine ((G.uniformExcess_walkDist_two_mul_le_aux hc hb).2 p hp).trans
    (mul_le_mul_of_nonneg_right ?_ (uniformExcess_nonneg hp))
  set n := Fintype.card V
  have hn : (1 : ℚ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hD0 : (0 : ℚ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
  have hDq : (D : ℚ) ≤ (n : ℚ) ^ 5 := by exact_mod_cast hD
  have h1 : (D : ℚ) ^ (2 * n) ≤ (n : ℚ) ^ (10 * n) := by
    calc (D : ℚ) ^ (2 * n) ≤ ((n : ℚ) ^ 5) ^ (2 * n) := pow_le_pow_left₀ hD0.le hDq _
      _ = (n : ℚ) ^ (10 * n) := by rw [← pow_mul]; ring_nf
  have h2 : 1 / (n : ℚ) ^ (10 * n) ≤ 1 / (D : ℚ) ^ (2 * n) :=
    one_div_le_one_div_of_le (by positivity) h1
  have h3 : 1 / (D : ℚ) ^ (2 * n) ≤ n * (1 / (D : ℚ) ^ (2 * n)) :=
    le_mul_of_one_le_left (by positivity) hn
  linarith

omit [Nonempty V] in
/-- A stationary `p` is fixed by every number of steps. -/
theorem IsStationary.walkDist_eq {p : V → ℚ} (h : G.IsStationary p) (k : ℕ) :
    G.walkDist p k = p := by
  induction k with
  | zero => exact G.walkDist_zero p
  | succ k ih => rw [walkDist_succ, show G.walkDist p 1 = p from h, ih]

/-- **[AB09, Exercise 7.11(b)(a)].** On a connected non-bipartite `D`-regular multigraph, the
uniform distribution is the only stationary distribution. -/
theorem isStationary_iff_eq_uniform (hc : G.Connected) (hb : ¬ G.IsBipartite) {p : V → ℚ}
    (hp : ∑ v, p v = 1) :
    G.IsStationary p ↔ p = fun _ => 1 / (Fintype.card V : ℚ) := by
  refine ⟨fun hs => ?_, fun h => h ▸ G.uniform_isStationary⟩
  obtain ⟨k, hk⟩ := G.exists_uniformExcess_walkDist_le hc hb
  set n := Fintype.card V
  have hn : (1 : ℚ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hε : 0 < 1 / (n : ℚ) ^ (10 * n) := by positivity
  have h := hk p hp
  rw [hs.walkDist_eq] at h
  have h0 : uniformExcess p ≤ 0 := by nlinarith [uniformExcess_nonneg hp]
  have hle : ∀ v, 0 ≤ 1 / (n : ℚ) - p v := fun v => by
    linarith [le_uniformExcess p v]
  have hsum : ∑ v, (1 / (n : ℚ) - p v) = 0 := by
    have := sum_sub_inv_card hp
    rw [show ∑ v, (1 / (n : ℚ) - p v) = -∑ v, (p v - 1 / (n : ℚ)) by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring, this,
      neg_zero]
  funext v
  have := (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hle v).mp hsum v (mem_univ v)
  linarith

/-- **[AB09, Exercise 7.11(b)(a)] over `ℝ`.** On a connected non-bipartite `D`-regular
multigraph, a real `p` of total mass one with `∑ᵤ p u·P(u, v) = p v` for all `v` is uniform.

**Proof sketch.** Stationarity iterates to `p = p·P^{2n}`, whose entries are positive
(`one_div_pow_le_transProb_two_mul`). At a maximiser `v` of `p`,
`∑ᵤ (p v − p u)·P^{2n}(u, v) = 0` has nonnegative terms, so `p` is constant. -/
theorem isStationary_real_iff_eq_uniform (hc : G.Connected) (hb : ¬ G.IsBipartite)
    {p : V → ℝ} (hp : ∑ v, p v = 1) :
    (∀ v, ∑ u, p u * (G.transProb 1 u v : ℝ) = p v) ↔
      p = fun _ => 1 / (Fintype.card V : ℝ) := by
  constructor
  · intro hs
    have hk : ∀ k v, ∑ u, p u * (G.transProb k u v : ℝ) = p v := by
      intro k
      induction k with
      | zero => intro v; simp [transProb_zero, apply_ite (fun q : ℚ => (q : ℝ))]
      | succ k ih =>
        intro v
        simp only [G.transProb_succ_eq_sum k, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum]
        rw [Finset.sum_comm, ← ih v]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← hs x, Finset.sum_mul]
        exact Finset.sum_congr rfl fun u _ => by ring
    set K := 2 * Fintype.card V
    have hpos : ∀ u v, (0 : ℝ) < G.transProb K u v := fun u v => by
      have hD : (0 : ℚ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
      have h := (by positivity : (0 : ℚ) < 1 / (D : ℚ) ^ K).trans_le
        (G.one_div_pow_le_transProb_two_mul hc hb u v)
      exact_mod_cast h
    obtain ⟨v, hv⟩ := Finite.exists_max p
    have hcol : ∑ u, (G.transProb K u v : ℝ) = 1 := by
      exact_mod_cast G.sum_transProb_left K v
    have hzero : ∑ u, (p v - p u) * (G.transProb K u v : ℝ) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hcol, hk K v, mul_one,
        sub_self]
    have hconst : ∀ u, p u = p v := fun u => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun u _ =>
        mul_nonneg (sub_nonneg.mpr (hv u)) (hpos u v).le).mp hzero u (mem_univ u)
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h (hpos u v).ne'
    have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hpv : p v = 1 / Fintype.card V := by
      rw [Finset.sum_congr rfl fun u _ => hconst u, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul] at hp
      field_simp
      linarith
    funext u
    rw [hconst u, hpv]
  · rintro rfl v
    have : ∑ u, (G.transProb 1 u v : ℝ) = 1 := by exact_mod_cast G.sum_transProb_left 1 v
    rw [← Finset.mul_sum, this, mul_one]

/-- **[AB09, Exercise 7.11(b)(b)].** On a connected non-bipartite `D`-regular multigraph, for
all sufficiently large `N` the expected number of times an `N`-step walk from `u` hits `v` is at
least `N/(2n)`.

**Proof sketch.** Iterating the contraction, `Δ` of the walk's distribution from `u` is
`≤ (1 − n^{−10n})^m ≤ 1/(4n²)` after `M = m·k` steps, and stays there; hence
`P^j(u, v) ≥ 1/n − n·Δ ≥ 3/(4n)` for `j ≥ M`, and for `N ≥ 3M` the sum
`expVisits_eq` is `≥ (N − M)·3/(4n) ≥ N/(2n)`. -/
theorem exists_le_expVisits (hc : G.Connected) (hb : ¬ G.IsBipartite) (u v : V) :
    ∃ N₀, ∀ N : ℕ, N₀ ≤ N → (N : ℚ) / (2 * Fintype.card V) ≤ G.expVisits v N u := by
  obtain ⟨K, hK⟩ := G.exists_uniformExcess_walkDist_le hc hb
  set n := Fintype.card V
  have hn : (1 : ℚ) ≤ n := by exact_mod_cast Fintype.card_pos
  set c : ℚ := 1 - 1 / (n : ℚ) ^ (10 * n)
  have hc0 : 0 ≤ c := by
    have : 1 / (n : ℚ) ^ (10 * n) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ hn
    simp only [c]; linarith
  have hc1 : c < 1 := by
    have : 0 < 1 / (n : ℚ) ^ (10 * n) := by positivity
    simp only [c]
    linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℚ) < 1 / (4 * n ^ 2)) hc1
  let e : V → ℚ := fun x => if x = u then 1 else 0
  have he : ∑ x, e x = 1 := by simp [e]
  have hwe : ∀ j, G.walkDist e j v = G.transProb j u v := fun j => by simp [walkDist, e]
  have he1 : uniformExcess e ≤ 1 := Finset.sup'_le _ _ fun x _ => by
    have : (0 : ℚ) ≤ 1 / n := by positivity
    simp only [e]; split_ifs <;> linarith
  set M := m * K
  have hlate : ∀ j, M ≤ j → 3 / (4 * n) ≤ G.transProb j u v := by
    intro j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    have hΔ : uniformExcess (G.walkDist e (M + d)) ≤ 1 / (4 * n ^ 2) := by
      rw [walkDist_add]
      calc uniformExcess (G.walkDist (G.walkDist e M) d) ≤ uniformExcess (G.walkDist e M) :=
            G.uniformExcess_walkDist_le_self (by rw [sum_walkDist, he]) d
        _ ≤ c ^ m * uniformExcess e := G.uniformExcess_walkDist_mul_le hc0 hK m he
        _ ≤ c ^ m := mul_le_of_le_one_right (pow_nonneg hc0 m) he1
        _ ≤ 1 / (4 * n ^ 2) := hm.le
    have hlow := inv_card_sub_le (p := G.walkDist e (M + d)) (by rw [sum_walkDist, he]) v
    rw [hwe] at hlow
    have : (n : ℚ) * uniformExcess (G.walkDist e (M + d)) ≤ 1 / (4 * n) := by
      calc (n : ℚ) * uniformExcess (G.walkDist e (M + d)) ≤ n * (1 / (4 * n ^ 2)) :=
            mul_le_mul_of_nonneg_left hΔ (by positivity)
        _ = 1 / (4 * n) := by field_simp
    have h34 : 3 / (4 * (n : ℚ)) = 1 / n - 1 / (4 * n) := by field_simp; ring
    linarith
  refine ⟨3 * M, fun N hN => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show M ≤ N by omega)
  rw [expVisits_eq, Finset.sum_range_add]
  have h1 : 0 ≤ ∑ j ∈ range M, G.transProb (j + 1) u v :=
    Finset.sum_nonneg fun j _ => G.transProb_nonneg _ _ _
  have h2 : (d : ℚ) * (3 / (4 * n)) ≤ ∑ j ∈ range d, G.transProb (M + j + 1) u v := by
    have := Finset.card_nsmul_le_sum (range d) (fun j => G.transProb (M + j + 1) u v)
      (3 / (4 * n)) fun j _ => hlate _ (by omega)
    simpa using this
  have hdM : (2 * M : ℚ) ≤ d := by exact_mod_cast (show 2 * M ≤ d by omega)
  have key : ((M + d : ℕ) : ℚ) / (2 * n) ≤ d * (3 / (4 * n)) := by
    rw [div_le_iff₀ (by positivity)]
    push_cast
    field_simp
    nlinarith
  linarith

end RegularMultigraph

end Randomized
