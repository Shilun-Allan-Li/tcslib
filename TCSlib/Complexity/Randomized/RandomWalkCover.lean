/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.RandomWalk
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.Bits

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Walks of fixed length on non-bipartite regular multigraphs

The combinatorial core of [AB09, Exercise 7.11(b)] (p.142): on a connected non-bipartite
`D`-regular multigraph with `n` vertices, any two vertices are joined by a walk of length
exactly `2n`, so every entry of the `2n`-step transition matrix is positive. The proof goes
through the bipartite double cover `V × Bool`, which is connected exactly when `G` is connected
and non-bipartite.

## Main definitions

* `Randomized.RegularMultigraph.endpoint` — the end of the walk along an index word.
* `Randomized.RegularMultigraph.Connected` — every vertex reaches every other.
* `Randomized.RegularMultigraph.IsBipartite` — some 2-colouring separates the two ends of every
  edge slot.

## Main results

* `Randomized.RegularMultigraph.exists_endpoint_eq_two_mul` — on a connected non-bipartite
  `G`, any two vertices are joined by a walk word of length exactly `2n`.

## Divergences

* [AB09] says "non-bipartite" for a graph; for the slot multigraph `IsBipartite` asks the
  2-colouring to separate the ends of every edge slot, so a self-loop rules it out.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

namespace RegularMultigraph

open Finset

variable {V : Type*} [DecidableEq V] {D : ℕ} (G : RegularMultigraph V D)

/-- The endpoint of the walk from `v` along the index word `w`. -/
def endpoint : V → List (Fin D) → V
  | v, [] => v
  | v, i :: w => endpoint (G.nbr v i) w

/-- The endpoint of a concatenated walk. -/
theorem endpoint_append (v : V) (w w' : List (Fin D)) :
    G.endpoint v (w ++ w') = G.endpoint (G.endpoint v w) w' := by
  induction w generalizing v with
  | nil => rfl
  | cons i w ih => exact ih _

/-- `G` is connected. -/
def Connected : Prop := ∀ u v, Relation.ReflTransGen G.Adj u v

/-- `G` is bipartite: a 2-colouring gives the two ends of every edge slot different colours
(a self-loop rules this out). -/
def IsBipartite : Prop := ∃ c : V → Bool, ∀ v i, c (G.nbr v i) ≠ c v

/-- Adjacency in the bipartite double cover of `G` on `V × Bool`: `(u, b) → (nbr u i, !b)`. -/
private def coverAdj (x y : V × Bool) : Prop := ∃ i, G.nbr x.1 i = y.1 ∧ y.2 = !x.2

/-- Double-cover adjacency is symmetric. -/
private theorem coverAdj_symm {x y : V × Bool} (h : G.coverAdj x y) : G.coverAdj y x := by
  obtain ⟨i, hi, h2⟩ := h
  obtain ⟨j, hj⟩ := G.adj_symm ⟨i, hi⟩
  exact ⟨j, hj, by rw [h2, Bool.not_not]⟩

/-- A walk in `G` lifts to the double cover from either sheet, with a fixed parity. -/
private theorem cover_lift {v w : V} (h : Relation.ReflTransGen G.Adj v w) :
    ∃ π : Bool, ∀ b, Relation.ReflTransGen G.coverAdj (v, b) (w, b ^^ π) := by
  induction h with
  | refl => exact ⟨false, fun b => by rw [Bool.xor_false]⟩
  | tail _ hxy ih =>
    obtain ⟨π, hπ⟩ := ih
    obtain ⟨i, hi⟩ := hxy
    exact ⟨!π, fun b => (hπ b).tail ⟨i, hi, by cases b <;> cases π <;> rfl⟩⟩

/-- A connected non-bipartite `G` has a connected double cover.

**Proof sketch.** Lift a walk `u → w` to the cover from sheet `false` (`cover_lift`), so every
`w` is reachable on some sheet. If some `w` is reachable on both sheets, route through `w` on
the sheet that makes the parity of the lifted `w → v` walk land on `(v, false)`. Otherwise
`w ↦ [(w, true) reachable]` gives the two ends of every edge slot different colours,
contradicting `¬ IsBipartite`. -/
private theorem cover_reach (hc : G.Connected) (hb : ¬ G.IsBipartite) (u v : V) :
    Relation.ReflTransGen G.coverAdj (u, false) (v, false) := by
  classical
  let S : V × Bool → Prop := fun x => Relation.ReflTransGen G.coverAdj (u, false) x
  have hall : ∀ w, ∃ c, S (w, c) := fun w => by
    obtain ⟨π, h⟩ := G.cover_lift (hc u w)
    exact ⟨false ^^ π, h false⟩
  by_cases hboth : ∃ w, S (w, false) ∧ S (w, true)
  · obtain ⟨w, h0, h1⟩ := hboth
    obtain ⟨π, h⟩ := G.cover_lift (hc w v)
    have hw : S (w, π) := by cases π; exacts [h0, h1]
    have := hw.trans (h π)
    rwa [Bool.xor_self] at this
  · push_neg at hboth
    exfalso
    apply hb
    have key : ∀ w, S (w, decide (S (w, true))) := fun w => by
      by_cases h : S (w, true)
      · simp [h]
      · obtain ⟨c, hc⟩ := hall w
        cases c
        · simpa [h] using hc
        · exact absurd hc h
    refine ⟨fun w => decide (S (w, true)), fun w i heq => ?_⟩
    have hstep : S (G.nbr w i, !decide (S (w, true))) := (key w).tail ⟨i, rfl, rfl⟩
    by_cases h : S (w, true)
    · simp only [h, decide_true, Bool.not_true] at hstep heq
      exact hboth _ hstep (of_decide_eq_true heq)
    · simp only [h, decide_false, Bool.not_false] at hstep heq
      exact absurd hstep (of_decide_eq_false heq)

/-- A walk in the double cover is an index word whose length has the parity of the sheet
change. -/
private theorem word_of_walk : ∀ {x y : V × Bool} (p : (SimpleGraph.fromRel G.coverAdj).Walk x y),
    ∃ w : List (Fin D), w.length = p.length ∧ G.endpoint x.1 w = y.1 ∧
      y.2 = (x.2 ^^ p.length.bodd)
  | _, _, .nil => ⟨[], rfl, rfl, by simp⟩
  | x, _, .cons (v := z) h p => by
    obtain ⟨w, hl, he, hb⟩ := word_of_walk p
    have hxz : G.coverAdj x z := by
      rcases ((SimpleGraph.fromRel_adj _ _ _).mp h).2 with h | h
      · exact h
      · exact G.coverAdj_symm h
    obtain ⟨i, hi, hi2⟩ := hxz
    refine ⟨i :: w, by simp [hl], by simp only [endpoint, hi, he], ?_⟩
    rw [SimpleGraph.Walk.length_cons, Nat.bodd_succ, hb, hi2]
    cases x.2 <;> cases p.length.bodd <;> rfl

/-- Between any two vertices there is a walk word of even length `< 2n`.

**Proof sketch.** `(u, false)` reaches `(v, false)` in the double cover (`cover_reach`); a
shortest such walk is a path, of length `< 2n`, and reads off as an index word whose length is
even because it starts and ends on the same sheet (`word_of_walk`). -/
private theorem exists_even_word [Fintype V] (hc : G.Connected) (hb : ¬ G.IsBipartite) (u v : V) :
    ∃ w : List (Fin D), w.length < 2 * Fintype.card V ∧ w.length % 2 = 0 ∧
      G.endpoint u w = v := by
  have key : ∀ {x y : V × Bool}, Relation.ReflTransGen G.coverAdj x y →
      (SimpleGraph.fromRel G.coverAdj).Reachable x y := by
    intro x y h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact SimpleGraph.Reachable.refl _
    | @head x y hxy _ ih =>
      have hne : x ≠ y := by
        obtain ⟨i, -, h2⟩ := hxy
        intro h; rw [h] at h2; cases hy : y.2 <;> simp [hy] at h2
      exact (SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).mpr
        ⟨hne, Or.inl hxy⟩)).trans ih
  obtain ⟨p⟩ := key (G.cover_reach hc hb u v)
  obtain ⟨w, hl, he, hb'⟩ := G.word_of_walk p.bypass
  have hlt := p.bypass_isPath.length_lt
  simp only [Fintype.card_prod, Fintype.card_bool] at hlt
  refine ⟨w, by rw [hl]; linarith, ?_, he⟩
  rw [hl, Nat.mod_two_of_bodd]
  cases h : p.bypass.length.bodd
  · rfl
  · simp [h] at hb'

/-- A walk word can be lengthened by any even number of steps (back and forth along an edge)
without changing its endpoint. -/
private theorem exists_word_add [NeZero D] {u v : V} (w : List (Fin D))
    (h : G.endpoint u w = v) :
    ∀ m, ∃ w' : List (Fin D), w'.length = w.length + 2 * m ∧ G.endpoint u w' = v
  | 0 => ⟨w, rfl, h⟩
  | m + 1 => by
    obtain ⟨w', hl, he⟩ := exists_word_add w h m
    let i : Fin D := ⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩
    obtain ⟨j, hj⟩ := G.adj_symm ⟨i, rfl⟩
    refine ⟨w' ++ [i, j], by simp [hl]; ring, ?_⟩
    rw [endpoint_append, he]
    exact hj

/-- On a connected non-bipartite `G`, any two vertices are joined by a walk word of length
exactly `2n` [AB09, Exercise 7.11(b)]. -/
theorem exists_endpoint_eq_two_mul [Fintype V] [NeZero D] (hc : G.Connected)
    (hb : ¬ G.IsBipartite) (u v : V) :
    ∃ w : List (Fin D), w.length = 2 * Fintype.card V ∧ G.endpoint u w = v := by
  obtain ⟨w, hlt, hev, he⟩ := G.exists_even_word hc hb u v
  obtain ⟨w', hl, he'⟩ := G.exists_word_add w he ((2 * Fintype.card V - w.length) / 2)
  exact ⟨w', by omega, he'⟩

end RegularMultigraph

end Randomized
