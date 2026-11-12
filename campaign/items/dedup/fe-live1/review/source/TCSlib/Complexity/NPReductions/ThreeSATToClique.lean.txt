/-
Copyright (c) 2026 Yangshuo Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangshuo Zou
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace ThreeSATToClique

/-!
# Formalisation of the 3-SAT → Clique Reduction

Given a 3-CNF formula `f` with `m` clauses, we construct a graph — the
*conflict graph* — whose vertices are pairs `(clause index, literal position)`
and whose edges connect vertices from *different* clauses whose literals are
*not* complementary.

The reduction is correct in both directions:

* **Completeness**: a satisfying assignment picks one true literal per clause;
  the corresponding vertices form a clique of size `m`, since they come from
  distinct clauses and no two true literals can conflict.

* **Soundness**: any `m`-clique must contain exactly one vertex per clause
  (the edge condition forbids two vertices from the same clause) and the
  selected literals are pairwise non-conflicting, so they admit a consistent
  truth assignment that satisfies every clause.

## Main definitions

* `CliqueVertex m` — a vertex `⟨c_idx, l_idx⟩` naming the `l_idx`-th literal
  of the `c_idx`-th clause.
* `getLitInClause`, `getLitAt` — extract the literal named by a vertex.
* `literalsConflict` — complementarity predicate on literals.
* `toCliqueGraph` — the conflict graph as a `SimpleGraph`.
* `hasClique` — existence of a `k`-clique.

## Main results

* `ThreeSAT_to_Clique_completeness`
* `ThreeSAT_to_Clique_soundness`
* `ThreeSAT_to_Clique_equivalence`
-/

-- =============================================================
-- Section 1. Propositional logic primitives
-- (Reproduced here so the file is self-contained.)
-- =============================================================

/-- A literal is either a positive or negative occurrence of a variable. -/
inductive Literal (V : Type)
  | pos (v : V)
  | neg (v : V)

/-- A clause is a disjunction, represented as a list of literals. -/
abbrev Clause (V : Type) := List (Literal V)

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNFFormula (V : Type) := List (Clause V)

/-- A truth valuation maps each variable to a proposition. -/
def Assignment (V : Type) := V → Prop

/-- The truth value of a literal under a given assignment. -/
def evalLiteral {V : Type} (α : Assignment V) : Literal V → Prop
  | .pos v => α v
  | .neg v => ¬(α v)

/-- A clause is satisfied if at least one of its literals is true. -/
def clauseSatisfied {V : Type} (α : Assignment V) (c : Clause V) : Prop :=
  ∃ l ∈ c, evalLiteral α l

/-- A CNF formula is satisfied if every clause is satisfied. -/
def formulaSatisfied {V : Type} (α : Assignment V) (f : CNFFormula V) : Prop :=
  ∀ c ∈ f, clauseSatisfied α c

/-- A CNF formula is satisfiable if some assignment satisfies it. -/
def isSatisfiable {V : Type} (f : CNFFormula V) : Prop :=
  ∃ α : Assignment V, formulaSatisfied α f

-- =============================================================
-- Section 2. 3-CNF primitives
-- =============================================================

/-- A 3-clause is a disjunction of exactly three literals. -/
structure Clause3 (V : Type) where
  l1 : Literal V
  l2 : Literal V
  l3 : Literal V

/-- A 3-CNF formula is a conjunction of 3-clauses. -/
abbrev Formula3 (V : Type) := List (Clause3 V)

/-- A 3-clause is satisfied if at least one of its three literals is true. -/
def clause3Satisfied {V : Type} (α : Assignment V) (c : Clause3 V) : Prop :=
  evalLiteral α c.l1 ∨ evalLiteral α c.l2 ∨ evalLiteral α c.l3

/-- A 3-CNF formula is satisfied if every 3-clause is satisfied. -/
def formula3Satisfied {V : Type} (α : Assignment V) (f : Formula3 V) : Prop :=
  ∀ c ∈ f, clause3Satisfied α c

/-- A 3-CNF formula is satisfiable if some assignment satisfies it. -/
def is3Satisfiable {V : Type} (f : Formula3 V) : Prop :=
  ∃ α : Assignment V, formula3Satisfied α f

-- =============================================================
-- Section 3. The conflict graph
-- =============================================================

/-- A vertex of the conflict graph names a literal by its clause index
    `c_idx : Fin m` and its position `l_idx : Fin 3` within that clause. -/
structure CliqueVertex (m : Nat) where
  c_idx : Fin m
  l_idx : Fin 3
deriving DecidableEq

/-- Extract the literal at position `p` from a 3-clause. -/
def getLitInClause {V : Type} (c : Clause3 V) : Fin 3 → Literal V
  | ⟨0, _⟩ => c.l1
  | ⟨1, _⟩ => c.l2
  | ⟨2, _⟩ => c.l3

/-- The literal named by vertex `v` in formula `f`.
    The type of `v` carries `f.length` so the index is always in bounds. -/
def getLitAt {V : Type} (f : Formula3 V) (v : CliqueVertex f.length) : Literal V :=
  getLitInClause (f.get v.c_idx) v.l_idx

/-- Two literals *conflict* if one is the positive and the other the negative
    occurrence of the same variable. -/
def literalsConflict {V : Type} (l1 l2 : Literal V) : Prop :=
  match l1, l2 with
  | .pos v1, .neg v2 => v1 = v2
  | .neg v1, .pos v2 => v1 = v2
  | _, _ => False

/-- `literalsConflict` is symmetric. -/
theorem literalsConflict_symm {V : Type} (l1 l2 : Literal V) :
    literalsConflict l1 l2 ↔ literalsConflict l2 l1 := by
  cases l1 <;> cases l2 <;> simp only [literalsConflict]
  · exact eq_comm
  · exact eq_comm

/-- The conflict graph of a 3-CNF formula `f`:
    * **vertices**: `CliqueVertex f.length`, i.e. pairs `(clause index, literal position)`.
    * **edges**: two vertices are adjacent iff they belong to *different* clauses
      and their respective literals do not conflict. -/
def toCliqueGraph {V : Type} (f : Formula3 V) : SimpleGraph (CliqueVertex f.length) where
  Adj u v := u.c_idx ≠ v.c_idx ∧ ¬ (literalsConflict (getLitAt f u) (getLitAt f v))
  symm u v := by
    intro ⟨hne, hnc⟩
    exact ⟨hne.symm, by rwa [literalsConflict_symm] at hnc⟩
  loopless u := by simp

/-- A graph `G` has a **`k`-clique** if there exists a set of `k` pairwise
    adjacent vertices. -/
def hasClique {V : Type} (G : SimpleGraph V) (k : Nat) : Prop :=
  ∃ (s : Finset V), s.card = k ∧ G.IsClique s

-- =============================================================
-- Section 4. Auxiliary lemmas
-- =============================================================

/-- Two simultaneously true literals cannot conflict: if `α` makes both `l1`
    and `l2` true, they cannot be complementary.

    *Proof*: complementarity forces `α v` and `¬ α v` for the same `v`. -/
lemma no_conflict_of_true {V : Type} (α : Assignment V) (l1 l2 : Literal V)
    (h1 : evalLiteral α l1) (h2 : evalLiteral α l2) : ¬ literalsConflict l1 l2 := by
  intro hc
  cases l1 <;> cases l2 <;> simp only [literalsConflict, evalLiteral] at hc h1 h2
  · -- l1 = .pos v1, l2 = .neg v2, conflict forces v1 = v2.
    rw [hc] at h1; exact h2 h1
  · -- l1 = .neg v1, l2 = .pos v2, conflict forces v1 = v2.
    rw [hc] at h1; exact h1 h2

/-- In an `m`-clique of the conflict graph, every clause index `i` is represented
    by *exactly one* vertex.

    *Proof sketch*: the clique has `m` vertices over `m` clauses; the edge
    condition forbids two vertices from the same clause (they would not be
    adjacent), so by a counting argument each clause contributes exactly one. -/
lemma clique_vertices_choose_one_per_clause {V : Type}
    (f : Formula3 V) (s : Finset (CliqueVertex f.length))
    (hcard : s.card = f.length) (hclique : (toCliqueGraph f).IsClique s) :
    ∀ (i : Fin f.length), ∃! u ∈ s, u.c_idx = i := by
  -- c_idx is injective on the clique: distinct clique vertices come from
  -- distinct clauses (forced by the edge condition).
  have h_inj_on : Set.InjOn (fun u : CliqueVertex f.length => u.c_idx) ↑s := by
    intro u hu v hv heq
    by_contra hne
    exact (hclique hu hv hne).1 heq
  -- Injective + same cardinality ⇒ image is everything.
  have h_image_univ : s.image (fun u => u.c_idx) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn h_inj_on, hcard, Fintype.card_fin]
  intro i
  obtain ⟨u, hu, hci⟩ := Finset.mem_image.mp (h_image_univ ▸ Finset.mem_univ i)
  refine ⟨u, ⟨hu, hci⟩, ?_⟩
  rintro v ⟨hv, hvi⟩
  exact (h_inj_on (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv)
    (hci.trans hvi.symm)).symm

/-- The literal named by vertex `v` with `v.c_idx = i` is one of the three
    literals of clause `f.get i`.

    This is used in the soundness proof to route the clique's chosen literal
    back to the original clause. -/
lemma getLitAt_mem_clause {V : Type} (f : Formula3 V) (v : CliqueVertex f.length)
    (i : Fin f.length) (h : v.c_idx = i) :
    getLitAt f v ∈ [(f.get i).l1, (f.get i).l2, (f.get i).l3] := by
  subst h
  dsimp [getLitAt]
  rcases hl : v.l_idx with ⟨val, isLt⟩
  rcases val with _ | _ | _ | n
  · simp [getLitInClause]
  · simp [getLitInClause]
  · simp [getLitInClause]
  · omega

-- =============================================================
-- Section 5. Main theorems
-- =============================================================

/-- **Completeness**: every satisfiable 3-CNF formula with `m` clauses has an
    `m`-clique in its conflict graph.

    *Proof*: from the satisfying assignment `α`, pick one true literal per clause
    (position `choice i` in clause `i`).  The resulting `m` vertices are pairwise
    adjacent because they come from distinct clauses and no two true literals
    conflict (`no_conflict_of_true`). -/
theorem ThreeSAT_to_Clique_completeness {V : Type} (f : Formula3 V) :
    is3Satisfiable f → hasClique (toCliqueGraph f) f.length := by
  rintro ⟨α, hsat⟩
  -- For each clause i, choose a position j such that the j-th literal is true.
  have h_choice : ∀ (i : Fin f.length), ∃ (j : Fin 3),
      evalLiteral α (getLitAt f (CliqueVertex.mk i j)) := by
    intro i
    have hclause := hsat (f.get i) (List.get_mem f i)
    rcases hclause with (h1 | h2 | h3)
    · exact ⟨0, h1⟩
    · exact ⟨1, h2⟩
    · exact ⟨2, h3⟩
  let choice (i : Fin f.length) : Fin 3 := (h_choice i).choose
  have hchoice_spec : ∀ i, evalLiteral α (getLitAt f ⟨i, choice i⟩) :=
    fun i => (h_choice i).choose_spec
  -- The clique: one vertex per clause, at the chosen position.
  let vertices : Finset (CliqueVertex f.length) :=
    Finset.univ.image (fun (i : Fin f.length) => CliqueVertex.mk i (choice i))
  -- The map i ↦ ⟨i, choice i⟩ is injective, so |vertices| = m.
  have hcard : vertices.card = f.length := by
    have hinj : Function.Injective (fun (i : Fin f.length) => CliqueVertex.mk i (choice i)) := by
      intro i j h; injection h
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin f.length]
  -- Any two distinct vertices are adjacent: different clauses, no conflict.
  have hclique : (toCliqueGraph f).IsClique vertices := by
    intro u hu v hv hne
    simp only [Finset.mem_coe, vertices] at hu hv
    rcases Finset.mem_image.mp hu with ⟨i, -, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨j, -, rfl⟩
    have hci_ne : i ≠ j := fun heq => hne (by simp [heq])
    exact ⟨by simpa using hci_ne,
           no_conflict_of_true α _ _ (hchoice_spec i) (hchoice_spec j)⟩
  exact ⟨vertices, hcard, hclique⟩

/-- **Soundness**: an `m`-clique in the conflict graph yields a satisfying
    assignment for the 3-CNF formula.

    *Proof outline*:
    1. By `clique_vertices_choose_one_per_clause`, each clause `i` has a unique
       representative vertex `uᵢ` in the clique.
    2. Define `α v = True` if some clique vertex names `.pos v`, and `False`
       if some clique vertex names `.neg v` (the clique's non-conflict condition
       ensures this is consistent).
    3. For each clause `i`, the literal at `uᵢ` is true under `α` and belongs
       to clause `i` by `getLitAt_mem_clause`, so the clause is satisfied. -/
theorem ThreeSAT_to_Clique_soundness {V : Type} (f : Formula3 V) :
    hasClique (toCliqueGraph f) f.length → is3Satisfiable f := by
  classical
  rintro ⟨s, hcard, hclique⟩
  have h_one_per_clause := clique_vertices_choose_one_per_clause f s hcard hclique
  -- α v is True iff some clique vertex names `.pos v`.
  let α : Assignment V := fun v =>
    if h : ∃ u ∈ s, getLitAt f u = .pos v then True
    else if h' : ∃ u ∈ s, getLitAt f u = .neg v then False
    else False
  -- Equivalent characterisation of α used throughout the proof.
  have hα_iff : ∀ v, α v ↔ ∃ u ∈ s, getLitAt f u = .pos v := by
    intro v
    change (if h : _ then True else _) ↔ _
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => trivial⟩
    · exact ⟨fun f => f.elim, fun hex => (h hex).elim⟩
    · exact ⟨fun f => f.elim, fun hex => (h hex).elim⟩
  -- Every literal at a clique vertex evaluates to true under α.
  have h_lit_true : ∀ u ∈ s, evalLiteral α (getLitAt f u) := by
    intro u hu
    cases hlit : getLitAt f u with
    | pos v =>
      simp only [evalLiteral]
      rw [hα_iff]
      exact ⟨u, hu, hlit⟩
    | neg v =>
      simp only [evalLiteral]
      rw [hα_iff]
      rintro ⟨u', hu', heq'⟩
      -- u and u' are both in the clique.  If u = u', then .neg v = .pos v.
      have hne : u ≠ u' := by
        intro heq; rw [heq] at hlit; rw [hlit] at heq'; cases heq'
      -- Otherwise u and u' are adjacent, but their literals conflict.
      have hadj := hclique (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hu') hne
      apply hadj.2
      rw [hlit, heq']
      rfl
  -- Build the satisfying assignment.
  refine ⟨α, ?_⟩
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
  obtain ⟨u, ⟨hu, hci⟩, _⟩ := h_one_per_clause i
  have hlit_true := h_lit_true u hu
  have hmem := getLitAt_mem_clause f u i hci
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with h | h | h
  · exact Or.inl (h ▸ hlit_true)
  · exact Or.inr (Or.inl (h ▸ hlit_true))
  · exact Or.inr (Or.inr (h ▸ hlit_true))

/-- **Equivalence**: a 3-CNF formula is satisfiable if and only if its conflict
    graph contains a clique of size equal to the number of clauses. -/
theorem ThreeSAT_to_Clique_equivalence {V : Type} (f : Formula3 V) :
    is3Satisfiable f ↔ hasClique (toCliqueGraph f) f.length :=
  ⟨ThreeSAT_to_Clique_completeness f, ThreeSAT_to_Clique_soundness f⟩

end ThreeSATToClique
