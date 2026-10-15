/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.RandomBits
import Mathlib.Logic.Relation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Field

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Random walks on regular multigraphs

The random walk behind [AB09, Theorem 7.19] (`UPATH ∈ RL`, p.139) and [AB09, Exercise 7.11]
(p.142): a walk on a `D`-regular undirected multigraph that, at each step, moves along a
uniformly random one of the `D` edge slots of the current vertex. Probabilities are exact
`ℚ` counting ratios, both over index words `Fin k → Fin D` and over fair-coin words.

## Main definitions

* `Randomized.RegularMultigraph` — a `D`-regular undirected multigraph with self-loops, as a
  neighbour function `nbr : V → Fin D → V` with symmetric edge multiplicities.
* `Randomized.idxProb` — the probability of an event over a uniform word in `(Fin D)^k`.
* `Randomized.RegularMultigraph.hits` — whether the walk along an index word visits `t`.
* `Randomized.RegularMultigraph.hitProb`, `missProb` — the probability that a `k`-step walk
  from `s` visits (avoids) `t`.
* `Randomized.decodeIdx` — reads `b` coins per step as an index in `Fin D`, `D = 2^b`.

## Main results

* `Randomized.RegularMultigraph.uniform_stationary` — [AB09, Exercise 7.11(a)].
* `Randomized.RegularMultigraph.hitProb_succ` — the one-step recursion of the walk.
* `Randomized.RegularMultigraph.randProb_hits_decodeIdx` — the coin-word probability equals
  the index-word probability.
* `Randomized.RegularMultigraph.reflTransGen_of_hits` — a walk only reaches connected vertices.

## Divergences

* [AB09] walks on an `n`-vertex regular graph and picks "a random neighbour". We fix the
  multigraph presentation by edge slots (`D` slots per vertex, self-loops and parallel edges
  allowed), which is what a log-space machine flipping `log₂ D` coins realizes; undirectedness
  is the symmetry `#{i | nbr u i = v} = #{i | nbr v i = u}`.
* Stationarity is proved directly in this exact `ℚ` slot model rather than bridged to
  `Expander.mulVec_uniform` (`Expanders/Basic.lean`), which works with real stochastic matrices.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset

/-- The probability that the event `A` holds of a uniformly random word `w ∈ (Fin D)^k`: the
counting ratio `#{w : A w}/D^k`. -/
def idxProb (D k : ℕ) (A : List (Fin D) → Prop) [DecidablePred A] : ℚ :=
  ((univ.filter fun w : Fin k → Fin D => A (List.ofFn w)).card : ℚ) / (D : ℚ) ^ k

/-- Over words of length `0`, an event has probability `1` or `0` according to `A []`. -/
theorem idxProb_zero (D : ℕ) (A : List (Fin D) → Prop) [DecidablePred A] :
    idxProb D 0 A = if A [] then 1 else 0 := by
  unfold idxProb
  rw [Finset.natCast_card_filter, Fintype.sum_unique]
  simp

/-- Conditioning on the first letter: `Pr_{(Fin D)^{k+1}}[A] = 𝔼_i Pr_{(Fin D)^k}[A(i :: ·)]`. -/
theorem idxProb_succ {D : ℕ} [NeZero D] (k : ℕ) (A : List (Fin D) → Prop)
    [DecidablePred A] :
    idxProb D (k + 1) A = (∑ i : Fin D, idxProb D k fun w => A (i :: w)) / D := by
  unfold idxProb
  have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  rw [Finset.natCast_card_filter, ← (Fin.consEquiv fun _ => Fin D).sum_comp, Fintype.sum_prod_type,
    ← Finset.sum_div, div_div, pow_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.natCast_card_filter]
  exact Finset.sum_congr rfl fun w _ => if_congr (by simp [List.ofFn_succ]) rfl rfl

/-- The certain event has probability one over `(Fin D)^k`, `D > 0`. -/
theorem idxProb_true {D : ℕ} [NeZero D] (k : ℕ) : idxProb D k (fun _ => True) = 1 := by
  unfold idxProb
  have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  rw [Finset.filter_true_of_mem fun _ _ => trivial]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  push_cast
  exact div_self (pow_ne_zero _ hD)

/-- A `D`-regular undirected multigraph with self-loops on the vertex type `V`: every vertex
has `D` edge slots, slot `i` of `v` leading to `nbr v i`, and the number of slots of `u`
leading to `v` equals the number of slots of `v` leading to `u` [AB09, Exercise 7.11]. -/
structure RegularMultigraph (V : Type*) [DecidableEq V] (D : ℕ) where
  /-- The endpoint of edge slot `i` at vertex `v`. -/
  nbr : V → Fin D → V
  /-- Undirectedness: edge multiplicities are symmetric. -/
  mult_symm : ∀ u v, (univ.filter fun i => nbr u i = v).card =
    (univ.filter fun i => nbr v i = u).card

namespace RegularMultigraph

variable {V : Type*} [DecidableEq V] {D : ℕ} (G : RegularMultigraph V D)

/-- The number of parallel edges from `u` to `v`. -/
def mult (u v : V) : ℕ := (univ.filter fun i => G.nbr u i = v).card

/-- `u` and `v` are adjacent: some edge slot of `u` leads to `v`. -/
def Adj (u v : V) : Prop := ∃ i, G.nbr u i = v

/-- Adjacency is symmetric. -/
theorem adj_symm {u v : V} (h : G.Adj u v) : G.Adj v u := by
  obtain ⟨i, hi⟩ := h
  have hpos : 0 < (univ.filter fun j => G.nbr u j = v).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  rw [G.mult_symm] at hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  exact ⟨j, (Finset.mem_filter.mp hj).2⟩

/-- Averaging a function over the `D` neighbours: one step of the walk's transition operator. -/
def avg (f : V → ℚ) (v : V) : ℚ := (∑ i, f (G.nbr v i)) / D

/-- A sum over the edge slots of `u` is a sum over vertices weighted by multiplicity. -/
theorem sum_nbr_eq [Fintype V] (u : V) (h : V → ℚ) :
    ∑ i, h (G.nbr u i) = ∑ v, (G.mult u v : ℚ) * h v := by
  rw [← Finset.sum_fiberwise univ (G.nbr u) (fun i => h (G.nbr u i))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2], Finset.sum_const,
    nsmul_eq_mul]
  rfl

/-- Reversibility: summing `g` over all directed edge slots is invariant under reversing
them. -/
theorem sum_swap [Fintype V] (g : V → V → ℚ) :
    ∑ u, ∑ i, g u (G.nbr u i) = ∑ u, ∑ i, g (G.nbr u i) u := by
  rw [Finset.sum_congr rfl fun u _ => G.sum_nbr_eq u (g u),
    Finset.sum_congr rfl fun u _ => G.sum_nbr_eq u (fun v => g v u), Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [mult, mult, G.mult_symm]

/-- Every vertex has in-degree `D`: `∑ᵤ mult u v = D`. -/
theorem sum_mult_left [Fintype V] (v : V) : ∑ u, (G.mult u v : ℚ) = D := by
  have h := G.sum_nbr_eq v (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [mult, mult, G.mult_symm]

/-- The uniform distribution is stationary: if `u` is uniform on the `n` vertices and one walk
step is taken, the result is uniform [AB09, Exercise 7.11(a)]. -/
theorem uniform_stationary [Fintype V] [NeZero D] (v : V) :
    ∑ u, (1 / Fintype.card V : ℚ) * (G.mult u v / D) = 1 / Fintype.card V := by
  have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  rw [← Finset.mul_sum, ← Finset.sum_div, G.sum_mult_left, div_self hD, mul_one]

/-- The averaging operator preserves total mass: `∑ᵥ avg f v = ∑ᵥ f v`. -/
theorem sum_avg [Fintype V] [NeZero D] (f : V → ℚ) : ∑ v, G.avg f v = ∑ v, f v := by
  have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  have h := G.sum_swap fun x _ => f x
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold avg
  rw [← Finset.sum_div, ← h, ← Finset.mul_sum, mul_div_cancel_left₀ _ hD]

/-- Whether the walk from `v` along the index word `w` visits `t` (at any of its
`|w| + 1` positions). -/
def hits (t : V) : V → List (Fin D) → Bool
  | v, [] => decide (v = t)
  | v, i :: w => decide (v = t) || hits t (G.nbr v i) w

/-- A walk visits only vertices connected to its start. -/
theorem reflTransGen_of_hits {t : V} :
    ∀ (s : V) (w : List (Fin D)), G.hits t s w = true → Relation.ReflTransGen G.Adj s t
  | s, [], h => by
    simp only [hits, decide_eq_true_eq] at h
    exact h ▸ Relation.ReflTransGen.refl
  | s, i :: w, h => by
    simp only [hits, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head ⟨i, rfl⟩ (reflTransGen_of_hits _ w h)

/-- The probability that a `k`-step random walk from `s` visits `t` (positions `0, …, k`). -/
def hitProb (t : V) (k : ℕ) (s : V) : ℚ := idxProb D k fun w => G.hits t s w = true

/-- The probability that a `k`-step random walk from `s` avoids `t`. -/
def missProb (t : V) (k : ℕ) (s : V) : ℚ := 1 - G.hitProb t k s

/-- A `0`-step walk visits `t` exactly when it starts there. -/
theorem hitProb_zero (t s : V) : G.hitProb t 0 s = if s = t then 1 else 0 := by
  unfold hitProb
  rw [idxProb_zero]
  simp [hits]

/-- One-step recursion: a walk from `t` has visited `t`; otherwise average over the first
step. -/
theorem hitProb_succ [NeZero D] (t : V) (k : ℕ) (s : V) :
    G.hitProb t (k + 1) s = if s = t then 1 else (∑ i, G.hitProb t k (G.nbr s i)) / D := by
  unfold hitProb
  rw [idxProb_succ]
  split_ifs with hs
  · have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
    simp only [hits, hs, decide_true, Bool.true_or]
    simp only [idxProb_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    exact div_self hD
  · simp [hits, hs]

/-- The miss probability satisfies the walk recursion with value `0` at `t`. -/
theorem missProb_succ [NeZero D] [Fintype V] (t : V) (k : ℕ) (s : V) :
    G.missProb t (k + 1) s = if s = t then 0 else G.avg (G.missProb t k) s := by
  have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  unfold missProb avg
  rw [hitProb_succ]
  split_ifs
  · ring
  · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sub_div, div_self hD]

/-- Hitting probabilities are nonnegative. -/
theorem hitProb_nonneg (t : V) (k : ℕ) (s : V) : 0 ≤ G.hitProb t k s := by
  unfold hitProb idxProb
  positivity

/-- Hitting probabilities are at most one. -/
theorem hitProb_le_one [NeZero D] (t : V) (k : ℕ) (s : V) : G.hitProb t k s ≤ 1 := by
  have hD : (0 : ℚ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
  unfold hitProb idxProb
  rw [div_le_one (pow_pos hD k)]
  calc ((univ.filter fun w : Fin k → Fin D => G.hits t s (List.ofFn w) = true).card : ℚ)
      ≤ ((univ : Finset (Fin k → Fin D)).card : ℚ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = (D : ℚ) ^ k := by simp

/-- Miss probabilities lie in `[0, 1]`. -/
theorem missProb_mem_Icc [NeZero D] (t : V) (k : ℕ) (s : V) :
    0 ≤ G.missProb t k s ∧ G.missProb t k s ≤ 1 := by
  unfold missProb
  constructor <;> linarith [G.hitProb_nonneg t k s, G.hitProb_le_one t k s]

end RegularMultigraph

/-- Reads `k` indices of `Fin D` from a coin word, `b` coins per index through the bijection
`e : {0,1}^b ≃ Fin D` (missing coins read as `false`). -/
def decodeIdx {b D : ℕ} (e : (Fin b → Bool) ≃ Fin D) : ℕ → List Bool → List (Fin D)
  | 0, _ => []
  | k + 1, l => e (fun j => l.getD j false) :: decodeIdx e k (l.drop b)

/-- Decoding a word that starts with the block `u` yields `e u` first. -/
theorem decodeIdx_succ_append {b D : ℕ} (e : (Fin b → Bool) ≃ Fin D) (k : ℕ)
    (u : Fin b → Bool) (l : List Bool) :
    decodeIdx e (k + 1) (List.ofFn u ++ l) = e u :: decodeIdx e k l := by
  have hu : (fun j : Fin b => (List.ofFn u ++ l).getD j false) = u := by
    funext j
    rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
    simp
  simp only [decodeIdx, hu, List.drop_left' (List.length_ofFn)]

namespace RegularMultigraph

variable {V : Type*} [DecidableEq V] {D : ℕ} (G : RegularMultigraph V D)

/-- **Coins realize the walk.** Reading `b` fair coins per step through a bijection
`{0,1}^b ≃ Fin D`, a `k`-step walk visits `t` with the same probability over coin words of
length `k·b` as over index words: `Pr_{r ∈ {0,1}^{kb}}[walk hits t] = hitProb t k s`.

**Proof sketch.** Both sides satisfy the recursion `hitProb_succ`: condition the coin word on
its first block (`randProb_append`), decode it by `decodeIdx_succ_append`, and reindex the
average over blocks by `e`, whose existence forces `2^b = D`. -/
theorem randProb_hits_decodeIdx {b : ℕ} (e : (Fin b → Bool) ≃ Fin D) (t : V) :
    ∀ (k : ℕ) (s : V),
      randProb (k * b) (fun l => G.hits t s (decodeIdx e k l) = true) = G.hitProb t k s := by
  have hcard : (2 : ℚ) ^ b = D := by
    have := Fintype.card_congr e
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    exact_mod_cast this
  haveI : NeZero D := ⟨by
    intro h; rw [h] at hcard; exact absurd hcard (by positivity)⟩
  intro k
  induction k with
  | zero =>
    intro s
    rw [hitProb_zero]
    unfold randProb
    simp only [zero_mul, decodeIdx, hits]
    split_ifs with hs <;> simp [hs]
  | succ k ih =>
    intro s
    rw [hitProb_succ, show (k + 1) * b = b + k * b by ring, randProb_append]
    simp only [decodeIdx_succ_append, hits]
    split_ifs with hs
    · simp only [hs, decide_true, Bool.true_or]
      simp only [randProb_true, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one]
      push_cast
      exact div_self (by positivity)
    · simp only [hs, decide_false, Bool.false_or, ih]
      rw [hcard]
      congr 1
      exact e.sum_comp (fun i => G.hitProb t k (G.nbr s i))

end RegularMultigraph

end Randomized
