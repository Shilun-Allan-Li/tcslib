/-
Copyright (c) 2026 Harsha Polavaram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Polavaram
-/

import TCSlib.GraphTheory.Kruskal.Reach

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Union-Find Correctness for Kruskal's Algorithm

## Main results

- `Kruskal.mergeAll_iff_reach`: merging all edges in a list yields the same partition iff there is a path (reachability) between the two nodes in the combined edge set
- `Kruskal.mergeAll_init_iff`: starting from the initial UF, mergeAll gives same partition iff the nodes are reachable in the edge list
- `Kruskal.mergeAll_perm`: merging a permutation of an edge list yields the same partition
- `Kruskal.merge_noop`: merging two nodes already in the same component leaves the UF unchanged

## References

- Original formalization by Harsha Polavaram
-/

namespace Kruskal

@[refl] lemma UF.SamePartition.rfl {n : ℕ} (uf : UF n) : UF.SamePartition uf uf :=
  fun _ _ => Iff.rfl

@[symm] lemma UF.SamePartition.symm {n : ℕ} {uf1 uf2 : UF n}
    (h : UF.SamePartition uf1 uf2) : UF.SamePartition uf2 uf1 :=
  fun i j => (h i j).symm

@[trans] lemma UF.SamePartition.trans {n : ℕ} {uf1 uf2 uf3 : UF n}
    (h1 : UF.SamePartition uf1 uf2) (h2 : UF.SamePartition uf2 uf3) :
    UF.SamePartition uf1 uf3 :=
  fun i j => (h1 i j).trans (h2 i j)

lemma merge_noop {n : ℕ} (uf : UF n) (i j : Fin n) (h : uf i = uf j) :
    uf.merge i j = uf := by
  funext k; unfold UF.merge; aesop

lemma mergeAll_preserves {n : ℕ} (uf : UF n) (edges : List (WEdge n))
    {a b : Fin n} (h : uf a = uf b) :
    (uf.mergeAll edges) a = (uf.mergeAll edges) b := by
  induction edges generalizing uf a b with
  | nil => exact h
  | cons g rest ih => exact ih _ (by unfold UF.merge; aesop)

lemma mergeAll_iff_reach {n : ℕ} (uf : UF n) (base edges : List (WEdge n))
    (huf : ∀ a b : Fin n, uf a = uf b ↔ Reach base a b) (a b : Fin n) :
    (uf.mergeAll edges) a = (uf.mergeAll edges) b ↔ Reach (base ++ edges) a b := by
  induction' edges with e edges ih generalizing uf base
  · convert huf a b using 1; simp +decide [Reach]
  · convert ih (uf.merge e.u e.v) (base ++ [e]) _ using 1
    · simp +decide [List.append_assoc]
    · intro a b; constructor <;> intro h <;> simp_all +decide [UF.merge]
      · split_ifs at h <;> simp_all +decide
        · have h_reach_base : Reach base a b :=
            (‹Reach base a e.v›).trans (reach_symm ‹Reach base b e.v›)
          exact reach_mono h_reach_base fun x hx => by aesop
        · have h_reach : Reach (base ++ [e]) a e.v ∧ Reach (base ++ [e]) e.u b :=
            ⟨reach_mono ‹_› fun x hx => List.mem_append_left _ hx,
             reach_mono ‹_› fun x hx => List.mem_append_left _ hx⟩
          have h_ev_eu : Reach (base ++ [e]) e.v e.u :=
            Relation.ReflTransGen.single ⟨e, by simp +decide, by simp +decide⟩
          exact h_reach.1.trans (h_ev_eu.trans h_reach.2)
        · have h_au : Reach (base ++ [e]) a e.u :=
            reach_mono h fun x hx => by aesop
          have h_euv : Reach (base ++ [e]) e.u e.v :=
            Relation.ReflTransGen.single ⟨e, by aesop⟩
          have h_vb : Reach (base ++ [e]) e.v b :=
            reach_symm <| reach_mono ‹_› fun x hx => by aesop
          exact h_au.trans (h_euv.trans h_vb)
        · exact reach_mono h fun x hx => List.mem_append_left _ hx
      · have h_reach : Reach base a b ∨ (Reach base a e.u ∧ Reach base e.v b) ∨
            (Reach base a e.v ∧ Reach base e.u b) := by
          convert reach_cons_iff.mp _
          convert reach_mono h _ using 1
          grind
        grind

lemma mergeAll_init_iff {n : ℕ} (edges : List (WEdge n)) (a b : Fin n) :
    (UF.init n).mergeAll edges a = (UF.init n).mergeAll edges b ↔ Reach edges a b := by
  convert mergeAll_iff_reach (UF.init n) [] edges _ a b
  intro a b; constructor <;> intro h <;> simp_all +decide [Reach]
  · cases a; cases b; aesop
  · induction h <;> simp_all +decide [SymAdj]

lemma mergeAll_congr {n : ℕ} {uf1 uf2 : UF n} (edges : List (WEdge n))
    (h : UF.SamePartition uf1 uf2) :
    UF.SamePartition (uf1.mergeAll edges) (uf2.mergeAll edges) := by
  unfold UF.SamePartition at h ⊢
  induction edges generalizing uf1 uf2 with
  | nil => exact h
  | cons e edges ih =>
    refine ih (uf1 := uf1.merge e.u e.v) (uf2 := uf2.merge e.u e.v) ?_
    intro i j; unfold UF.merge; grind

lemma merge_swap_partition {n : ℕ} (uf : UF n) (a b : WEdge n) :
    UF.SamePartition
      ((uf.merge a.u a.v).merge b.u b.v)
      ((uf.merge b.u b.v).merge a.u a.v) := by
  intros i j
  by_cases hi : uf i = uf a.u <;> by_cases hj : uf j = uf a.u <;>
    simp +decide [*, UF.merge] <;> grind

lemma mergeAll_perm {n : ℕ} (uf : UF n) {l1 l2 : List (WEdge n)}
    (hp : l1.Perm l2) :
    UF.SamePartition (uf.mergeAll l1) (uf.mergeAll l2) := by
  induction hp generalizing uf with
  | nil => rfl
  | cons _ _ ih => exact ih _
  | swap a b _ => exact mergeAll_congr _ (merge_swap_partition uf b a)
  | trans _ _ ih1 ih2 => exact (ih1 _).trans (ih2 _)

lemma mergeAll_append_single {n : ℕ} (uf : UF n) (l : List (WEdge n)) (e : WEdge n) :
    (uf.mergeAll (l ++ [e])) = (uf.mergeAll l).merge e.u e.v := by
  induction l generalizing uf with
  | nil => rfl
  | cons _ _ ih => exact ih _

lemma mergeAll_cons_eq {n : ℕ} (uf : UF n) (e : WEdge n) (S : List (WEdge n)) :
    UF.SamePartition (uf.mergeAll (e :: S)) ((uf.merge e.u e.v).mergeAll S) :=
  UF.SamePartition.rfl _

lemma erase_append_perm {n : ℕ} {l : List (WEdge n)} {e : WEdge n} (he : e ∈ l) :
    l.Perm (l.erase e ++ [e]) := by grind

end Kruskal
