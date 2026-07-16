import Mathlib

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace Kruskal
structure WEdge (n : ℕ) where
  u : Fin n
  v : Fin n
  weight : ℕ
  deriving Repr, DecidableEq
end Kruskal

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace Kruskal
def SymAdj {n : ℕ} (edges : List (WEdge n)) (u v : Fin n) : Prop :=
  ∃ e ∈ edges, (e.u = u ∧ e.v = v) ∨ (e.u = v ∧ e.v = u)
end Kruskal

namespace Kruskal
def Reach {n : ℕ} (edges : List (WEdge n)) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen (SymAdj edges)
end Kruskal

namespace Kruskal
lemma symAdj_symm {n : ℕ} {edges : List (WEdge n)} {u v : Fin n}
    (h : SymAdj edges u v) : SymAdj edges v u :=
  h.imp fun _ he => ⟨he.1, he.2.symm⟩
end Kruskal

namespace Kruskal
lemma symAdj_mono {n : ℕ} {e1 e2 : List (WEdge n)} {u v : Fin n}
    (h : SymAdj e1 u v) (hs : ∀ e ∈ e1, e ∈ e2) : SymAdj e2 u v :=
  h.imp fun _ he => ⟨hs _ he.1, he.2⟩
end Kruskal

namespace Kruskal
lemma reach_symm {n : ℕ} {edges : List (WEdge n)} {u v : Fin n}
    (h : Reach edges u v) : Reach edges v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hcd ih =>
    exact (Relation.ReflTransGen.single (symAdj_symm hcd)).trans ih
end Kruskal

namespace Kruskal
lemma reach_mono {n : ℕ} {e1 e2 : List (WEdge n)} {u v : Fin n}
    (h : Reach e1 u v) (hs : ∀ e ∈ e1, e ∈ e2) : Reach e2 u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hcd ih => exact ih.tail (symAdj_mono hcd hs)
end Kruskal

namespace Kruskal
lemma reach_of_mem {n : ℕ} {edges : List (WEdge n)} {e : WEdge n}
    (he : e ∈ edges) : Reach edges e.u e.v :=
  Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
end Kruskal

namespace Kruskal
lemma reach_cons_iff {n : ℕ} {g : WEdge n} {rest : List (WEdge n)} {a b : Fin n} :
    Reach (g :: rest) a b ↔
      Reach rest a b ∨
      (Reach rest a g.u ∧ Reach rest g.v b) ∨
      (Reach rest a g.v ∧ Reach rest g.u b) := by
  have mono : ∀ {x y}, Reach rest x y → Reach (g :: rest) x y :=
    fun h => reach_mono h fun _ => List.mem_cons_of_mem _
  have gadj : Reach (g :: rest) g.u g.v :=
    Relation.ReflTransGen.single ⟨g, List.mem_cons_self .., Or.inl ⟨rfl, rfl⟩⟩
  refine ⟨fun h => ?_, ?_⟩
  · induction' h with c d hcd ih
    · exact Or.inl .refl
    · rcases ih with ⟨e, he, he'⟩
      rcases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all +decide [Reach]
      · rcases he with rfl | he
        · aesop
        · rename_i h
          rcases h with h | h | h
          · exact Or.inl <| h.tail ⟨e, he, by tauto⟩
          · exact Or.inr <| Or.inl ⟨h.1, h.2.tail ⟨e, he, by tauto⟩⟩
          · exact Or.inr <| Or.inr ⟨h.1, h.2.tail ⟨e, he, by tauto⟩⟩
      · -- Backward edge: c = e.v, b = e.u. Use the IH for e.v, then reverse via e.
        rename_i h
        rcases he with rfl | he
        · -- e = g: IH is about g.v, goal is about g.u
          rcases h with h | ⟨h1, _⟩ | ⟨h1, _⟩
          · exact Or.inr (Or.inr ⟨h, .refl⟩)
          · exact Or.inl h1
          · exact Or.inr (Or.inr ⟨h1, .refl⟩)
        · -- e ∈ rest: Reach rest e.v e.u by symmetry, then chain
          have hrev := reach_symm (reach_of_mem he)
          rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl (h.trans hrev)
          · exact Or.inr (Or.inl ⟨h1, h2.trans hrev⟩)
          · exact Or.inr (Or.inr ⟨h1, h2.trans hrev⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact mono h
    · exact (mono h1).trans (gadj.trans (mono h2))
    · exact (mono h1).trans ((reach_symm gadj).trans (mono h2))
end Kruskal
