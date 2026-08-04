/-
Copyright (c) 2026 Harsha Polavaram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Polavaram
-/

import TCSlib.GraphTheory.Kruskal.UnionFind
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exchange Argument for Kruskal's Algorithm

## Main results

- `Kruskal.exchange_with_base`: Given a spanning set and an edge that connects two previously
  disconnected components, there exists an edge in the set that can be swapped for the new edge
  while preserving connectivity.
- `Kruskal.uf_exchange`: Union-find version of the exchange argument: swapping an edge in a
  spanning set for a lighter edge yields a partition-equivalent union-find state.
- `Kruskal.reduce_to_rest`: If an edge is redundant (its endpoints are already connected),
  there exists a subset of the remaining edges with equal or lesser total weight that spans
  the same partition.

## References

- Original formalization by Harsha Polavaram
-/

namespace Kruskal

lemma exchange_take_head {n : ℕ} {base rest : List (WEdge n)} {g e : WEdge n}
    (h1 : Reach (base ++ rest) e.u g.u) (h2 : Reach (base ++ rest) g.v e.v) :
    ∀ a b, Reach (base ++ g :: rest) a b → Reach (base ++ rest ++ [e]) a b := by
  have mono : ∀ {x y}, Reach (base ++ rest) x y → Reach (base ++ rest ++ [e]) x y :=
    fun h => reach_mono h fun _ hx => List.mem_append_left _ hx
  have he_adj : Reach (base ++ rest ++ [e]) e.u e.v :=
    reach_of_mem (by simp)
  intro a b h
  apply reach_lift (edges := base ++ g :: rest) _ h
  intro c d ⟨f, hmem, hadj⟩
  by_cases hfg : f = g
  · subst hfg
    rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ((reach_symm (mono h1)).trans he_adj).trans (reach_symm (mono h2))
    · exact ((mono h2).trans (reach_symm he_adj)).trans (mono h1)
  · refine Relation.ReflTransGen.single ⟨f, ?_, hadj⟩
    simp only [List.mem_append, List.mem_cons] at hmem ⊢
    tauto

lemma exchange_take_head' {n : ℕ} {base rest : List (WEdge n)} {g e : WEdge n}
    (h1 : Reach (base ++ rest) e.u g.v) (h2 : Reach (base ++ rest) g.u e.v) :
    ∀ a b, Reach (base ++ g :: rest) a b → Reach (base ++ rest ++ [e]) a b := by
  intro a b hab
  refine exchange_take_head (g := ⟨g.v, g.u, g.weight⟩) h1 h2 a b ?_
  apply reach_lift (edges := base ++ g :: rest) _ hab
  intro x y hxy
  exact Relation.ReflTransGen.single (by unfold SymAdj at *; aesop)

lemma exchange_with_base {n : ℕ} {base S : List (WEdge n)} {e : WEdge n}
    (hreach : Reach (base ++ S) e.u e.v)
    (hbase : ¬Reach base e.u e.v) (hne : e.u ≠ e.v) :
    ∃ f ∈ S, ∀ a b, Reach (base ++ S) a b →
      Reach (base ++ S.erase f ++ [e]) a b := by
  revert e
  intro e hreach hbase hne
  induction' S with g S ih generalizing base
  · aesop
  · by_cases hcase1 : Reach (base ++ S) e.u e.v
    · specialize ih hcase1 hbase
      obtain ⟨f, hf1, hf2⟩ := ih
      simp_all +decide [List.erase_cons]
      refine Or.inr ⟨f, hf1, fun a b hab => ?_⟩
      split_ifs <;> simp_all +decide
      · apply reach_lift
        rotate_right
        exact base ++ f :: S
        · intro a b hab
          exact reach_mono (by tauto) (by aesop)
        · assumption
      · have h_reach : Reach (base ++ S) a b ∨
            (Reach (base ++ S) a g.u ∧ Reach (base ++ S) g.v b) ∨
            (Reach (base ++ S) a g.v ∧ Reach (base ++ S) g.u b) := by
          have h_iff : Reach (base ++ g :: S) a b ↔ Reach (base ++ S) a b ∨
              (Reach (base ++ S) a g.u ∧ Reach (base ++ S) g.v b) ∨
              (Reach (base ++ S) a g.v ∧ Reach (base ++ S) g.u b) := by
            convert reach_cons_iff using 1
            convert reach_mem_iff _ using 1
            grind
          exact h_iff.mp hab
        rcases h_reach with h | h | h
        · exact reach_mono (hf2 a b h) fun x hx => by aesop
        · have h1 : Reach (base ++ g :: (S.erase f ++ [e])) a g.u :=
            reach_mono (hf2 _ _ h.1) fun x hx => by aesop
          have h2 : Reach (base ++ g :: (S.erase f ++ [e])) g.v b :=
            reach_mono (hf2 _ _ h.2) fun x hx => by aesop
          have hg : Reach (base ++ g :: (S.erase f ++ [e])) g.u g.v :=
            Relation.ReflTransGen.single ⟨g, by aesop⟩
          exact h1.trans (hg.trans h2)
        · have h1 : Reach (base ++ g :: (S.erase f ++ [e])) a g.v :=
            reach_mono (hf2 _ _ h.1) fun x hx => by aesop
          have h2 : Reach (base ++ g :: (S.erase f ++ [e])) g.u b :=
            reach_mono (hf2 _ _ h.2) fun x hx => by aesop
          have hg : Reach (base ++ g :: (S.erase f ++ [e])) g.v g.u :=
            reach_symm (reach_of_mem (by simp +decide :
              g ∈ base ++ g :: (S.erase f ++ [e])))
          exact h1.trans (hg.trans h2)
    · have hswap : Reach (base ++ S) e.u g.u ∧ Reach (base ++ S) g.v e.v ∨
          Reach (base ++ S) e.u g.v ∧ Reach (base ++ S) g.u e.v := by
        have hreach_g : Reach (g :: (base ++ S)) e.u e.v :=
          (reach_mem_iff (by grind)).1 hreach
        cases reach_cons_iff.mp hreach_g <;> aesop
      cases' hswap with hswap hswap
      · have hlift : ∀ a b, Reach (base ++ g :: S) a b → Reach (base ++ S ++ [e]) a b :=
          exchange_take_head hswap.left hswap.right
        aesop
      · have hlift : ∀ a b, Reach (base ++ g :: S) a b → Reach (base ++ S ++ [e]) a b :=
          exchange_take_head' hswap.1 hswap.2
        use g; simp
        simpa only [List.append_assoc] using hlift

lemma uf_exchange {n : ℕ} (uf : UF n) (base S : List (WEdge n)) (e : WEdge n)
    (huf : ∀ a b : Fin n, uf a = uf b ↔ Reach base a b)
    (hconn : (uf.mergeAll S) e.u = (uf.mergeAll S) e.v)
    (hdiff : uf e.u ≠ uf e.v) :
    ∃ f ∈ S, UF.SamePartition
      ((uf.merge e.u e.v).mergeAll (S.erase f))
      (uf.mergeAll S) := by
  obtain ⟨f, hfS, hswap⟩ : ∃ f ∈ S, ∀ a b, Reach (base ++ S) a b →
      Reach (base ++ S.erase f ++ [e]) a b := by
    apply exchange_with_base
    · exact (mergeAll_iff_reach uf base S huf e.u e.v).mp hconn
    · exact fun h => hdiff <| (huf _ _).2 h
    · contrapose! hdiff; aesop
  have hswap_symm : ∀ a b, Reach (base ++ S.erase f ++ [e]) a b → Reach (base ++ S) a b := by
    intro a b hab
    apply reach_lift (edges := base ++ S.erase f ++ [e]) _ hab
    intro a b ⟨g, hg, hg'⟩
    rcases List.mem_append.mp hg with hg1 | hg1
    · rcases List.mem_append.mp hg1 with hg2 | hg2
      · exact reach_mono (.single ⟨g, hg2, hg'⟩) (fun x hx => List.mem_append_left _ hx)
      · exact reach_mono (.single ⟨g, List.mem_of_mem_erase hg2, hg'⟩)
              (fun x hx => List.mem_append_right _ hx)
    · have hge : e = g := (List.mem_singleton.mp hg1).symm
      subst hge
      have hreach_e : Reach (base ++ S) e.u e.v :=
        (mergeAll_iff_reach uf base S huf e.u e.v).mp hconn
      rcases hg' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hreach_e
      · exact reach_symm hreach_e
  have hcomp_S : ∀ a b, (uf.mergeAll S) a = (uf.mergeAll S) b ↔ Reach (base ++ S) a b :=
    mergeAll_iff_reach uf base S huf
  have hcomp_S' : ∀ a b, ((uf.merge e.u e.v).mergeAll (S.erase f)) a =
      ((uf.merge e.u e.v).mergeAll (S.erase f)) b ↔ Reach (base ++ S.erase f ++ [e]) a b := by
    have hcomp_e : ∀ a b, ((uf.merge e.u e.v).mergeAll (S.erase f)) a =
        ((uf.merge e.u e.v).mergeAll (S.erase f)) b ↔ Reach (base ++ [e] ++ S.erase f) a b := by
      apply mergeAll_iff_reach
      convert mergeAll_iff_reach uf base [e] huf using 1
    simp_all +decide [List.append_assoc]
    apply reach_mem_iff; grind
  exact ⟨f, hfS, fun a b => by aesop⟩

lemma reduce_to_rest {n : ℕ} (uf : UF n) (e : WEdge n) (rest S : List (WEdge n))
    (hSsub : ∀ x ∈ S, x ∈ e :: rest)
    (hSspan : UF.SamePartition (uf.mergeAll S) (uf.mergeAll rest))
    (hred : uf e.u = uf e.v) :
    ∃ S' : List (WEdge n),
      (∀ x ∈ S', x ∈ rest) ∧
      UF.SamePartition (uf.mergeAll S') (uf.mergeAll rest) ∧
      totalWeight S' ≤ totalWeight S := by
  revert hSspan hSsub hred
  have mergeAll_filter_redundant (uf : UF n) (S : List (WEdge n)) (e : WEdge n)
      (rest : List (WEdge n))
      (hSsub : ∀ x ∈ S, x ∈ e :: rest) (hred : uf e.u = uf e.v) :
      UF.SamePartition (uf.mergeAll (S.filter (fun x => decide (x ∈ rest))))
        (uf.mergeAll S) := by
    induction' S with x S ih generalizing uf
    · exact UF.SamePartition.rfl _
    · by_cases hx : x ∈ rest <;> simp_all +decide
      · convert ih (uf.merge x.u x.v) _ using 1
        unfold UF.merge; aesop
      · convert ih uf hred using 1
        rw [show uf.mergeAll (e :: S) = (uf.merge e.u e.v).mergeAll S from by rfl]
        rw [merge_noop _ _ _ hred]
  intro hSsub hSspan hred
  refine ⟨S.filter (fun x => decide (x ∈ rest)), ?_, ?_, ?_⟩
  · intro x hx; simp at hx; exact hx.2
  · exact (mergeAll_filter_redundant uf S e rest hSsub hred).trans hSspan
  · unfold totalWeight
    have hle : ∀ l : List (WEdge n),
        (List.map WEdge.weight (l.filter (fun x => decide (x ∈ rest)))).sum ≤
          (List.map WEdge.weight l).sum := by
      intro l
      induction l with
      | nil => simp
      | cons x l ih =>
        by_cases hx : x ∈ rest <;> simp [hx] <;> linarith
    exact hle S

end Kruskal
