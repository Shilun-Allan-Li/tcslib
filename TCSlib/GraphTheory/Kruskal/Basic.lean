/-
Copyright (c) 2026 Harsha Polavaram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Polavaram
-/

import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Lemma
import Mathlib.Data.List.Sort

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Kruskal's Algorithm — Core Definitions

## Main results

- `Kruskal.kruskal_subset`: every edge returned by the Kruskal algorithm belongs to the input edge list
- `Kruskal.processEdges_mem`: every edge in the output of `processEdges` comes from the accumulator or the input list

## References

- Original formalization by Harsha Polavaram
-/

namespace Kruskal

structure WEdge (n : ℕ) where
  u : Fin n
  v : Fin n
  weight : ℕ
  deriving Repr, DecidableEq

def UF (n : ℕ) := Fin n → ℕ

namespace UF

def init (n : ℕ) : UF n := fun i => i.val

def find {n : ℕ} (uf : UF n) (i : Fin n) : ℕ := uf i

def merge {n : ℕ} (uf : UF n) (i j : Fin n) : UF n :=
  let cj := uf j
  let ci := uf i
  fun k => if uf k = cj then ci else uf k

@[simp] lemma init_find {n : ℕ} (i : Fin n) : (init n).find i = i.val := rfl
@[simp] lemma find_def {n : ℕ} (uf : UF n) (i : Fin n) : uf.find i = uf i := rfl

def mergeAll {n : ℕ} (uf : UF n) : List (WEdge n) → UF n
  | [] => uf
  | e :: rest => (uf.merge e.u e.v).mergeAll rest

def SamePartition {n : ℕ} (uf1 uf2 : UF n) : Prop :=
  ∀ i j : Fin n, uf1 i = uf1 j ↔ uf2 i = uf2 j

end UF

def processEdges {n : ℕ} : List (WEdge n) → UF n → List (WEdge n) → List (WEdge n)
  | [], _, acc => acc.reverse
  | e :: rest, uf, acc =>
    if uf.find e.u ≠ uf.find e.v then
      processEdges rest (uf.merge e.u e.v) (e :: acc)
    else
      processEdges rest uf acc

def kruskal (n : ℕ) (edges : List (WEdge n)) : List (WEdge n) :=
  let sorted := edges.mergeSort (fun e₁ e₂ => decide (e₁.weight ≤ e₂.weight))
  processEdges sorted (UF.init n) []

lemma processEdges_mem {n : ℕ} (edges : List (WEdge n)) (uf : UF n)
    (acc : List (WEdge n)) (e : WEdge n) (he : e ∈ processEdges edges uf acc) :
    e ∈ acc ∨ e ∈ edges := by
  induction edges generalizing uf acc with
  | nil => exact Or.inl (List.mem_reverse.mp he)
  | cons e' rest ih =>
    simp only [processEdges] at he
    split_ifs at he with h
    · rcases ih _ _ he with h' | h'
      · rcases List.mem_cons.mp h' with rfl | h'
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')
    · rcases ih _ _ he with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')

lemma kruskal_subset {n : ℕ} (edges : List (WEdge n)) (e : WEdge n)
    (he : e ∈ kruskal n edges) : e ∈ edges := by
  rcases processEdges_mem _ _ _ _ he with h | h
  · cases h
  · exact List.mem_mergeSort.mp h

end Kruskal
