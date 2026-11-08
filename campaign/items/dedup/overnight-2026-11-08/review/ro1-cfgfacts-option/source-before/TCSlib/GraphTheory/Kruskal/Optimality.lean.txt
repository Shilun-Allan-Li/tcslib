/-
Copyright (c) 2026 Harsha Polavaram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Polavaram
-/

import TCSlib.GraphTheory.Kruskal.Exchange

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Optimality of Kruskal's Algorithm

## Main results

- `Kruskal.processEdges_optimal`: The greedy edge-selection loop produces a spanning subgraph of weight at most any competing spanning subset, proved by induction with an exchange argument.
- `Kruskal.kruskal_spans`: The output of Kruskal's algorithm spans the same vertices as the input edge list.
- `Kruskal.kruskal_optimal`: The total weight of Kruskal's output is minimal among all spanning subsets of the input.

## References

- Original formalization by Harsha Polavaram
-/

namespace Kruskal

def ufAfterProcessEdges {n : ℕ} : List (WEdge n) → UF n → UF n
  | [], uf => uf
  | e :: rest, uf =>
    if uf.find e.u ≠ uf.find e.v then ufAfterProcessEdges rest (uf.merge e.u e.v)
    else ufAfterProcessEdges rest uf

lemma ufAfterProcessEdges_partition {n : ℕ} (edges : List (WEdge n)) (uf : UF n) :
    UF.SamePartition (ufAfterProcessEdges edges uf) (uf.mergeAll edges) := by
  induction edges generalizing uf with
  | nil => rfl
  | cons e edges ih =>
    unfold ufAfterProcessEdges
    split_ifs with h
    · exact ih _
    · have heq : uf e.u = uf e.v := Classical.not_not.1 h
      change (ufAfterProcessEdges edges uf).SamePartition ((uf.merge e.u e.v).mergeAll edges)
      rw [merge_noop _ _ _ heq]
      exact ih _

lemma processEdges_acc {n : ℕ} (edges : List (WEdge n)) (uf : UF n)
    (acc : List (WEdge n)) :
    processEdges edges uf acc = acc.reverse ++ processEdges edges uf [] := by
  induction edges generalizing uf acc with
  | nil => simp [processEdges]
  | cons e edges ih =>
    simp only [processEdges]
    split_ifs with h
    · rw [ih (uf.merge e.u e.v) (e :: acc), ih (uf.merge e.u e.v) [e]]; simp
    · exact ih uf acc

lemma processEdges_same_partition {n : ℕ} (edges : List (WEdge n)) (uf : UF n) :
    UF.SamePartition
      (uf.mergeAll (processEdges edges uf []))
      (uf.mergeAll edges) := by
  convert ufAfterProcessEdges_partition edges uf using 1
  induction edges generalizing uf with
  | nil => rfl
  | cons e edges ih =>
    simp only [processEdges, ufAfterProcessEdges]
    by_cases h : uf.find e.u ≠ uf.find e.v
    · rw [if_pos h, if_pos h, processEdges_acc]
      simp [UF.mergeAll, ih]
    · rw [if_neg h, if_neg h]; exact ih _

lemma processEdges_skip {n : ℕ} {e : WEdge n} {rest : List (WEdge n)} {uf : UF n}
    (h : uf.find e.u = uf.find e.v) :
    processEdges (e :: rest) uf [] = processEdges rest uf [] := if_neg (by aesop)

lemma processEdges_take_weight {n : ℕ} {e : WEdge n} {rest : List (WEdge n)} {uf : UF n}
    (h : uf.find e.u ≠ uf.find e.v) :
    totalWeight (processEdges (e :: rest) uf []) =
      e.weight + totalWeight (processEdges rest (uf.merge e.u e.v) []) := by
  rw [show processEdges (e :: rest) uf [] = if uf.find e.u ≠ uf.find e.v then
    processEdges rest (uf.merge e.u e.v) [e] else processEdges rest uf [] from rfl,
    if_pos h, processEdges_acc, List.reverse_singleton]
  rfl

lemma processEdges_optimal {n : ℕ}
    (edges : List (WEdge n)) (uf : UF n) (base : List (WEdge n))
    (huf : ∀ a b : Fin n, uf a = uf b ↔ Reach base a b)
    (S : List (WEdge n)) (hSsub : ∀ e ∈ S, e ∈ edges)
    (hSspan : UF.SamePartition (uf.mergeAll S) (uf.mergeAll edges))
    (hsorted : List.Pairwise (fun e1 e2 => e1.weight ≤ e2.weight) edges) :
    totalWeight (processEdges edges uf []) ≤ totalWeight S := by
  induction' edges with e edges ih generalizing uf base S
  · simp [processEdges, totalWeight]
  · by_cases he : uf.find e.u = uf.find e.v
    · obtain ⟨S', hS'sub, hS'span, hS'weight⟩ :
          ∃ S', (∀ e ∈ S', e ∈ edges) ∧
            (uf.mergeAll S').SamePartition (uf.mergeAll edges) ∧
            totalWeight S' ≤ totalWeight S := by
        apply reduce_to_rest
        · exact hSsub
        · convert hSspan.trans _ using 1
          convert mergeAll_cons_eq uf e edges using 1
          rw [merge_noop]; aesop
        · exact he
      rw [processEdges_skip he]
      exact le_trans (ih uf base huf S' hS'sub hS'span
        ((List.pairwise_cons.mp hsorted).2)) hS'weight
    · by_cases heS : e ∈ S <;> simp_all +decide [processEdges_take_weight]
      · have hS'_subset : UF.SamePartition
            ((uf.merge e.u e.v).mergeAll (S.erase e))
            ((uf.merge e.u e.v).mergeAll edges) := by
          have hp1 : UF.SamePartition (uf.mergeAll (S.erase e ++ [e]))
              (uf.mergeAll (e :: edges)) :=
            (mergeAll_perm uf (erase_append_perm heS).symm).trans hSspan
          have hp2 : UF.SamePartition ((uf.merge e.u e.v).mergeAll (S.erase e))
              (uf.mergeAll (S.erase e ++ [e])) :=
            (by convert mergeAll_perm uf (show List.Perm (S.erase e ++ [e])
                (e :: S.erase e) from by grind) using 1 :
              UF.SamePartition (uf.mergeAll (S.erase e ++ [e]))
                ((uf.merge e.u e.v).mergeAll (S.erase e))).symm
          convert hp2.trans ‹_› using 1
        obtain ⟨S', hS'_subset, hS'_span, hS'_weight⟩ :=
          reduce_to_rest (uf.merge e.u e.v) e edges (S.erase e)
            (by grind) hS'_subset (by simp [UF.merge])
        have := ih (uf.merge e.u e.v) (base ++ [e])
          (by intros a b
              convert mergeAll_iff_reach uf base [e] huf a b using 1)
          S' hS'_subset hS'_span
        linarith [totalWeight_erase S e heS]
      · obtain ⟨f, hfS, hf⟩ : ∃ f ∈ S, UF.SamePartition
            ((uf.merge e.u e.v).mergeAll (S.erase f)) (uf.mergeAll S) := by
          apply uf_exchange
          · exact huf
          · exact (hSspan _ _).2 ((mergeAll_iff_reach uf base (e :: edges) huf _ _).2
              (Relation.ReflTransGen.single (by exact ⟨e, by aesop⟩)))
          · exact fun h => he <| (huf _ _).1 h
        obtain ⟨S', hS'sub, hS'span, hS'weight⟩ : ∃ S' : List (WEdge n),
            (∀ x ∈ S', x ∈ edges) ∧
            UF.SamePartition ((uf.merge e.u e.v).mergeAll S')
              ((uf.merge e.u e.v).mergeAll edges) ∧
            totalWeight S' ≤ totalWeight (S.erase f) := by
          apply reduce_to_rest
          any_goals exact e
          · grind
          · refine hf.trans ?_; convert hSspan using 1
          · unfold UF.merge; aesop
        have := ih (uf.merge e.u e.v) (base ++ [e])
          (by convert mergeAll_iff_reach uf base [e] huf using 1) S' hS'sub hS'span
        have hfedges : f ∈ edges := by
          rcases hSsub f hfS with rfl | h
          · exact absurd hfS heS
          · exact h
        linarith [totalWeight_erase S f hfS, hsorted.1 f hfedges]

theorem kruskal_spans {n : ℕ} (E : List (WEdge n)) : SpansLike (kruskal n E) E := by
  intro u v huv
  set sorted := E.mergeSort (fun e₁ e₂ => decide (e₁.weight ≤ e₂.weight))
  have h_sorted : Reach sorted u v :=
    reach_mono huv fun _ he => List.mem_mergeSort.mpr he
  have h_span := processEdges_same_partition sorted (UF.init n)
  exact (mergeAll_init_iff _ _ _).mp <|
    (h_span u v).2 ((mergeAll_init_iff _ _ _).2 h_sorted)

theorem kruskal_optimal {n : ℕ} (E S : List (WEdge n))
    (hSsub : ∀ e ∈ S, e ∈ E) (hSspan : SpansLike S E) :
    totalWeight (kruskal n E) ≤ totalWeight S := by
  refine processEdges_optimal _ _ [] ?_ S ?_ ?_ ?_
  · intro a b
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases Fin.ext h; exact Relation.ReflTransGen.refl
    · induction h with
      | refl => rfl
      | tail _ hcd _ => obtain ⟨_, h, _⟩ := hcd; cases h
  · exact fun e he => List.mem_mergeSort.mpr (hSsub e he)
  · intro a b
    rw [mergeAll_init_iff, mergeAll_init_iff]
    refine ⟨fun h => reach_mono h fun e he => List.mem_mergeSort.mpr (hSsub e he),
      fun h => hSspan a b <| reach_mono h fun e he => List.mem_mergeSort.mp he⟩
  · have h := List.sorted_mergeSort
      (le := fun e₁ e₂ : WEdge n => decide (e₁.weight ≤ e₂.weight))
      (by intro a b c; simp; exact le_trans) (by intro a b; simp; exact le_total _ _) E
    exact h.imp (by intro a b h; simpa using h)

end Kruskal
