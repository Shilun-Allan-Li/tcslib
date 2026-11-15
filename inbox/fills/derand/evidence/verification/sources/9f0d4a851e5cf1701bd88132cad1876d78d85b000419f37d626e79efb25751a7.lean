/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Random walks fail on directed graphs

[AB09, Exercise 7.10]: the random-walk algorithm for connectivity does not work for directed
graphs. On the digraph with vertices `0, …, n` and edges `i → i + 1`, `i → 0`, there is a
directed path from `s = 0` to `t = n`, yet the walk reaches `t` within `T` steps with
probability at most `(T + 1)/2ⁿ`, so its expected hitting time is at least `(2ⁿ − 1)/2`.

The walk moves from `v` to a uniformly random out-neighbour. Probabilities are exact `ℚ`
values; as in `TCSlib.Complexity.Randomized.RandomWalkHitting`, the expected hitting time is
read through the tail sums `hitTime t N s = ∑_{j<N} Pr[the j-step walk from s avoids t]`.

## Main definitions

* `Randomized.outNbrs`, `Randomized.avgOut` — out-neighbours, and the average over them.
* `Randomized.hitProb` — `Pr[the k-step walk from s visits t]`, by first-step analysis.
* `Randomized.hitTime` — the truncated expected hitting time.
* `Randomized.chainDigraph` — the digraph `i → i + 1`, `i → 0` on `Fin (n + 1)`.

## Main results

* `Randomized.chainDigraph_reachable` — a directed path leads from `0` to `n`.
* `Randomized.hitProb_chainDigraph_le` — `Pr[reach n within T steps] ≤ (T + 1)/2ⁿ`.
* `Randomized.hitTime_chainDigraph_ge` — [AB09, Exercise 7.10]: `(2ⁿ − 1)/2 ≤ 𝔼[τ]`.

## Divergences

* `hitProb` is defined by the first-step recursion of the walk (stop on `t`, else average
  over a uniform out-neighbour), not as a measure on paths. A vertex without out-neighbours
  keeps the walk in place; the example digraph has none.
* `Randomized.RegularMultigraph.hitProb`/`hitTime` are not reused: they need a `D`-regular
  symmetric multigraph, while here out-degrees vary and edges are directed.
* The example has `n + 1` vertices; the bound `Ω(2ⁿ)` is the book's up to the constant `2`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]

/-- The out-neighbours of `v`. -/
def outNbrs (v : V) : Finset V := univ.filter (G.Adj v)

/-- The expected value of `f` after one step from `v`: the average of `f` over the
out-neighbours of `v`, or `f v` when `v` has none. -/
def avgOut (f : V → ℚ) (v : V) : ℚ :=
  if (outNbrs G v).Nonempty then (∑ u ∈ outNbrs G v, f u) / (outNbrs G v).card else f v

/-- `Pr[the k-step walk from s visits t]`, where each step moves to a uniformly random
out-neighbour: `1` at `t`, otherwise the one-step average of the `(k−1)`-step probability. -/
def hitProb (t : V) : ℕ → V → ℚ
  | 0, s => if s = t then 1 else 0
  | k + 1, s => if s = t then 1 else avgOut G (hitProb t k) s

/-- The truncated expected hitting time `∑_{j<N} Pr[the j-step walk from s avoids t]`, the
expectation of `min(τ, N)` for the hitting time `τ` of `t`. -/
def hitTime (t : V) (N : ℕ) (s : V) : ℚ :=
  ∑ j ∈ range N, (1 - hitProb G t j s)

end General

/-- The digraph on `Fin (n + 1)` with edges `i → i + 1` and `i → 0`. [AB09, Exercise 7.10] -/
def chainDigraph (n : ℕ) : Digraph (Fin (n + 1)) where
  Adj i j := j = 0 ∨ (j : ℕ) = i + 1

instance (n : ℕ) : DecidableRel (chainDigraph n).Adj := fun i j =>
  inferInstanceAs (Decidable (j = 0 ∨ (j : ℕ) = i + 1))

/-- A directed path leads from `0` to `n` (the statement is GraphTheory's `Digraph.Reachable`,
`GraphTheory/Core/DirectedGraphs.lean`, unfolded). -/
theorem chainDigraph_reachable (n : ℕ) :
    Relation.ReflTransGen (chainDigraph n).Adj 0 (Fin.last n) := by
  suffices h : ∀ i (hi : i < n + 1), Relation.ReflTransGen (chainDigraph n).Adj 0 ⟨i, hi⟩ from
    h n (Nat.lt_succ_self n)
  intro i
  induction i with
  | zero => exact fun _ => Relation.ReflTransGen.refl
  | succ i ih =>
    intro hi
    exact (ih (by omega)).tail (Or.inr rfl)

/-- Below the last vertex the walk moves to `0` or to `i + 1`, each with probability `1/2`. -/
theorem avgOut_chainDigraph {n : ℕ} (f : Fin (n + 1) → ℚ) (i : Fin (n + 1)) (hi : (i : ℕ) < n) :
    avgOut (chainDigraph n) f i = (f 0 + f ⟨i + 1, by omega⟩) / 2 := by
  have hne : (0 : Fin (n + 1)) ≠ ⟨i + 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hset : outNbrs (chainDigraph n) i = {0, ⟨i + 1, by omega⟩} := by
    ext j
    simp only [outNbrs, chainDigraph, mem_filter, mem_univ, true_and, mem_insert,
      mem_singleton, Fin.ext_iff]
  have hnon : (outNbrs (chainDigraph n) i).Nonempty := by rw [hset]; simp
  rw [avgOut, if_pos hnon, hset, sum_pair hne, card_pair hne]
  norm_num

/-- The hitting probability of `n` from `i` within `k` steps is at most `(2^i + k)/2ⁿ`.

**Proof sketch.** Induction on `k`. At `n` the bound is `≥ 1`. Below `n`, the walk moves to
`0` or `i + 1` with probability `1/2` each, so by induction the probability is at most
`((1 + k) + (2^{i+1} + k))/(2·2ⁿ) ≤ (2^i + k + 1)/2ⁿ`. -/
theorem hitProb_chainDigraph_le_aux (n k : ℕ) (i : Fin (n + 1)) :
    hitProb (chainDigraph n) (Fin.last n) k i * 2 ^ n ≤ 2 ^ (i : ℕ) + k := by
  have h2 : (0 : ℚ) < 2 ^ n := by positivity
  induction k generalizing i with
  | zero =>
    by_cases hi : i = Fin.last n
    · subst hi
      simp [hitProb]
    · simp only [hitProb, if_neg hi, zero_mul, Nat.cast_zero, add_zero]
      positivity
  | succ k ih =>
    by_cases hi : i = Fin.last n
    · subst hi
      simp only [hitProb, if_true, one_mul, Fin.val_last, Nat.cast_succ]
      linarith [show (0 : ℚ) ≤ k from Nat.cast_nonneg k]
    · have hlt : (i : ℕ) < n := by
        have := i.isLt
        have : (i : ℕ) ≠ n := fun h => hi (Fin.ext h)
        omega
      simp only [hitProb, if_neg hi]
      rw [avgOut_chainDigraph _ i hlt]
      have h0 := ih 0
      have h1 := ih ⟨i + 1, by omega⟩
      simp only [Fin.val_zero, pow_zero] at h0
      simp only [pow_succ] at h1
      push_cast
      nlinarith

/-- **Reaching `t` is exponentially unlikely**: on `chainDigraph n`, the walk from `0` visits
`n` within `T` steps with probability at most `(T + 1)/2ⁿ`. [AB09, Exercise 7.10] -/
theorem hitProb_chainDigraph_le (n T : ℕ) :
    hitProb (chainDigraph n) (Fin.last n) T 0 ≤ (T + 1) / 2 ^ n := by
  have h := hitProb_chainDigraph_le_aux n T 0
  simp only [Fin.val_zero, pow_zero] at h
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `∑_{j<N} (j + 1) = N(N + 1)/2` over `ℚ`. -/
private theorem sum_range_succ_cast (N : ℕ) :
    ∑ j ∈ range N, ((j : ℚ) + 1) = N * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- **The expected hitting time is exponential** [AB09, Exercise 7.10]: on `chainDigraph n`,
the walk from `0` needs in expectation at least `(2ⁿ − 1)/2` steps to reach `n`, although a
directed path leads there (`chainDigraph_reachable`): every bound `B` on the truncated
expected hitting times is at least `(2ⁿ − 1)/2`.

**Proof sketch.** By `hitProb_chainDigraph_le`, `hitTime (2ⁿ) ≥ ∑_{j<2ⁿ} (1 − (j+1)/2ⁿ)
= 2ⁿ − (2ⁿ + 1)/2`. -/
theorem hitTime_chainDigraph_ge (n : ℕ) {B : ℚ}
    (hB : ∀ N, hitTime (chainDigraph n) (Fin.last n) N 0 ≤ B) :
    (2 ^ n - 1) / 2 ≤ B := by
  refine le_trans ?_ (hB (2 ^ n))
  have h2 : (0 : ℚ) < 2 ^ n := by positivity
  have hsum : ∑ j ∈ range (2 ^ n), (1 - ((j : ℚ) + 1) / 2 ^ n) ≤
      hitTime (chainDigraph n) (Fin.last n) (2 ^ n) 0 :=
    Finset.sum_le_sum fun j _ => by linarith [hitProb_chainDigraph_le n j]
  refine le_trans (le_of_eq ?_) hsum
  rw [sum_sub_distrib, ← sum_div, sum_range_succ_cast]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  push_cast
  field_simp
  ring

end Randomized
