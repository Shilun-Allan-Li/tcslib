/-
Copyright (c) 2026 UC Berkeley CS 294. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CS 294-268 course staff (UC Berkeley, Spring 2026)
         Lecturer: Venkatesan Guruswami

This file formalises the NAE-SAT → 3-Coloring reduction.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# NAE-SAT and 3-COLORING

## NAE-SAT
The **Not-All-Equal Satisfiability** problem asks: Given a set Boolean variables
`x_1, ..., x_n`, and a set of "clauses" `C_1, ... , C_m`, where each clause
is a triple of variables, does there exist a Boolean assigment such that
the variables in each clause `C_i` do not all get the same value.

## 3-COLORING
The **3-COLORING** problem asks: Given a graph, does there exists a `3`-coloring
such that no two vertices that share an edge get the same color.

## Reduction from NAE-SAT to 3-COLORING

Given a NAE-SAT instance over variables `x_1, ... , x_n` and clauses
`C_1, ... , C_m`, we create an instance of 3-COLORING over a graph over the
following vertices:
* A "ground" node `⊥`
* A "variable" node `x_i`
* Three "clause" nodes `c_{j,1}`, `c_{j,2}`, `c_{j,3}`.

The edges over this graph are defined as follows:
* The ground vertex `⊥` is connected to each variable vertex `x_i`.
* For a clause `c_r` containing variables `x_i`, `x_j` and `x_k`, we connect
  * `x_i`, `x_j`, `x_k` to `c_{r, 1}`, `c_{r, 2}`, `c_{r, 3}` respectively.
  * `c_{r, 1}`, `c_{r, 2}` and `c_{r,3}` are all interconnected.

This is visualized below:
        ⊥
        |
  +-----+-----+
  |     |     |
 x_1   x_2   x_3
  |     |     |
 c_1---c_2---c_3
  |           |
  +-----------+

**Proof Sketch.**

_Completeness:_

Given an assignment for the NAE-SAT instance, we construct a 3-coloring of the
reduction graph as follows:
* The ground node is colored `0`.
* If a variable `x_i` is assigned `true`, then the corresponding variable node
  is colored `1`; otherwise, it is colored `2`.
* For each clause `C_r = (x_i, x_j, x_k)`, the clause nodes `c_{r,1}`,
  `c_{r,2}`, and `c_{r,3}` are colored based on the truth assignments of
  `x_i`, `x_j`, and `x_k` such that they are all colored differently. This is
  always possible since not all literals in the clause have the same value.

_Soundness:_

Given a 3-coloring of the reduction graph, we construct an assignment for the
NAE-SAT instance as follows:
* If a variable node `x_i` is colored `1`, then the corresponding variable
  `x_i` is assigned `true`; otherwise, it is assigned `false`.
Since the clause nodes are connected in a triangle, they must have different
colors. Also, each clause node is connected to the corresponding variable node,
so the variables in each clause cannot all have the same value.

## Main results
- NAEtoColorReduction: IsSatisfiable f ↔ Is3Colorable (ReductionGraph f)

## References
- Course material from CS 294-268 (UC Berkeley, Spring 2026), V. Guruswami
-/

namespace NAEtoColor

/-- A Not-All-Equal Clause -/
structure NAEclause (V : Type) where
  v0 : V
  v1 : V
  v2 : V

/-- Evaluate a Not-All-Equal clause -/
def SatisfiesClause {V : Type} (assign : V → Bool) (c : NAEclause V) : Bool :=
  (
    assign c.v0 ≠ assign c.v1 ||
    assign c.v0 ≠ assign c.v2 ||
    assign c.v1 ≠ assign c.v2
  )

/-- A NAE-SAT instance is a list of NAE clauses. -/
abbrev NAESat3 (V : Type) := List (NAEclause V)

/-- Returns `true` if the assignment satisfies all clauses. -/
def SatisfiesNAE3 {V : Type} (assign : V → Bool) (f : NAESat3 V) : Bool :=
  f.all (SatisfiesClause assign)

/-- The satisfiability property for a NAE-SAT instance. -/
noncomputable def IsSatisfiable {V : Type} (f : NAESat3 V) : Prop :=
  ∃ (assign : V → Bool), SatisfiesNAE3 assign f = true

-- Some examples to test definitions:
namespace NAE_SAT_Example

def nae_sat_eg : NAESat3 (Fin 5) := [⟨0, 1, 2⟩, ⟨0, 1, 3⟩, ⟨0, 2, 4⟩]

def assign_eg := ![true, true, false, false, false]

#eval SatisfiesClause assign_eg nae_sat_eg[2]
#eval SatisfiesNAE3 assign_eg nae_sat_eg

example : IsSatisfiable nae_sat_eg := ⟨assign_eg, rfl⟩
  -- Equivalent to `by use ex_assign_1; rfl`

end NAE_SAT_Example

/-- A simple graph is 3-colorable if there exists a valid 3-coloring.

Equivalently, a valid 3-coloring is equivalent to a graph homomorphism from
the given simple graph to the 3-Clique.
-/
def Is3Colorable {V' : Type} (G : SimpleGraph V') : Prop :=
  Nonempty (G.Coloring (Fin 3))

/-- Vertex set for reduction from NAE-SAT to 3-COLORING.
We map the input variables to output vertices using an inductive type.
This cleanly separates the three kinds of vertices without any integer indexing:
• groundNode  – 1 ground node, who color is 0 (assume True = 1, False = 2).
• varNode     – 1 node per variable.
• clauseNode  – 3 internal nodes per clause that encode the NAE constraint.
-/
inductive OutputVertex (V : Type)
| groundNode                                 -- ground vertex colored "neutral"
| varNode (v : V)                            -- one node per variable
| clauseNode (c : NAEclause V) (idx : Fin 3) -- 3 nodes per clause

/-- Edge relation for reduction from NAE-SAT to 3-COLORING.

The edges over this graph are defined as follows:
* The ground vertex `⊥` is connected to each variable vertex `x_i`.
* For a clause `c_r` containing variables `x_i`, `x_j` and `x_k`, we connect
  * `x_i`, `x_j`, `x_k` to `c_{r, 1}`, `c_{r, 2}`, `c_{r, 3}` respectively.
  * `c_{r, 1}`, `c_{r, 2}` and `c_{r,3}` are all interconnected.

This is visualized below:
        ⊥
        |
  +-----+-----+
  |     |     |
 x_1   x_2   x_3
  |     |     |
 c_1---c_2---c_3
  |           |
  +-----------+
-/
def EdgeRelation {V : Type} (clauses : NAESat3 V) (u v: OutputVertex V) : Prop :=
  match u, v with
  -- Connect ground vertex with every variable node.
  | .groundNode, .varNode _ => True
  | .varNode _, .groundNode => True

  -- Connect variable node to corresponding clause nodes.
  | .varNode v, .clauseNode c i =>
    (v = c.v0 ∧ i = 0) ∨ (v = c.v1 ∧ i = 1) ∨ (v = c.v2 ∧ i = 2)
  | .clauseNode c i, .varNode v =>
    (v = c.v0 ∧ i = 0) ∨ (v = c.v1 ∧ i = 1) ∨ (v = c.v2 ∧ i = 2)

  -- Connect clause gadgets to each other
  | .clauseNode c1 i, .clauseNode c2 j => c1 = c2 ∧ c1 ∈ clauses ∧ i ≠ j

  -- If a pair of vertices doesn't match any of the above patterns, there is no edge.
  | _, _ => False

/-- Simple graph for reduction from NAE-SAT to 3-Coloring.

We symmetrize EdgeRelation manually so proof of symmetry becomes trivial.
A SimpleGraph also requires irreflexivity (no self-loops), enforced by `u ≠ v`,
so we encode that in adjacency as well.
-/
def ReductionGraph {V : Type} (f : NAESat3 V) : SimpleGraph (OutputVertex V) where
  Adj u v := u ≠ v ∧ (EdgeRelation f u v ∨ EdgeRelation f v u)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless := fun _ h => h.1 rfl

/-- Coloring of clause nodes obtained via reduction from NAE-SAT.

Given the boolean values of the three literals in a clause, assigns colors to
the three internal clause-gadget nodes.
We do not assume that the clause is in the NAE-SAT instance.
If the variables do not satisfy the Not-All-Equal clause, we color everything 0.
This is a valid coloring since there are no edges between clause nodes in that
case, and all variable nodes are colored either 1 or 2.
-/
private def clauseNodeColor (a b c : Bool) (k : Fin 3) : Fin 3 :=
  match a, b, c with
  | true,  true,  false => match k with | 0 => 0 | 1 => 2 | 2 => 1
  | true,  false, true  => match k with | 0 => 0 | 1 => 1 | 2 => 2
  | false, true,  true  => match k with | 0 => 1 | 1 => 0 | 2 => 2
  | true,  false, false => match k with | 0 => 2 | 1 => 0 | 2 => 1
  | false, true,  false => match k with | 0 => 0 | 1 => 2 | 2 => 1
  | false, false, true  => match k with | 0 => 0 | 1 => 1 | 2 => 2
  | _,     _,     _     => 0  -- (non-NAE cases have no clause-clause edges)

/-- Coloring of entire simple graph obtained via reduction from NAE-SAT.
Coloring constructed from NAE-SAT assignment.
  • groundNode      ↦  0
  • varNode v       ↦  1 if assign v = true, else 2
  • clauseNode c k  ↦  clauseNodeColor (assign values of the 3 variables)
-/
private def naeColoring {V : Type} (assign : V → Bool) : OutputVertex V → Fin 3
  | .groundNode => 0
  | .varNode v => if assign v then 1 else 2
  | .clauseNode c k => clauseNodeColor (assign c.v0) (assign c.v1) (assign c.v2) k

/-- Completeness of reduction from NAE-SAT to 3-Coloring. -/
lemma NAEtoColorCompleteness {V : Type} (f : NAESat3 V) :
  IsSatisfiable f → Is3Colorable (ReductionGraph f) := by
  intro ⟨assign, hsat⟩
  refine ⟨⟨naeColoring assign, ?_⟩⟩
  intro u v hadj
  simp only [SimpleGraph.top_adj]
  obtain ⟨hne, hedge⟩ := hadj
  -- Prove for any directed edge; then handle both directions
  suffices ∀ {a b : OutputVertex V}, EdgeRelation f a b →
              naeColoring assign a ≠ naeColoring assign b by
    rcases hedge with h | h'
    · exact this h
    · exact fun heq => this h' heq.symm
  intro a b h
  match a, b with
  -- There are 6 cases to match:
  -- 1. Ground node : Ground node (no edge)
  | .groundNode, .groundNode => exact False.elim h
  -- 2. Ground node : Var node
  | .groundNode, .varNode v | .varNode v, .groundNode =>
      simp only [naeColoring]
      cases assign v <;> simp
  -- 3. Ground node : Clause node (no edge)
  | .groundNode, .clauseNode _ _ | .clauseNode _ _, .groundNode =>
    exact False.elim h
  -- 4. Var node : Var node (no edge)
  | .varNode v, .varNode w => exact False.elim h
  -- 5. Var node : Clause node
  | .varNode v, .clauseNode c k | .clauseNode c k, .varNode v =>
    simp only [EdgeRelation] at h
    simp only [naeColoring]
    -- After rcases, k is substituted to 0, 1, or 2 by the rfl
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (cases assign c.v0 <;> cases assign c.v1 <;> cases assign c.v2 <;>
       simp [clauseNodeColor])
  -- 6. Clause node : Clause node
  | .clauseNode c1 i, .clauseNode c2 j =>
    obtain ⟨rfl, hcIn, hij⟩ := h
    simp only [naeColoring]
    have hNAE : SatisfiesClause assign c1 = true :=
      List.all_eq_true.mp hsat c1 hcIn
    -- Case-split on both indices and all boolean assignments.
    -- Diagonal (i=j): hij gives contradiction. Non-diagonal non-NAE: hNAE gives contradiction.
    fin_cases i <;> fin_cases j <;>
      cases h0 : assign c1.v0 <;> cases h1 : assign c1.v1 <;> cases h2 : assign c1.v2 <;>
      simp_all [clauseNodeColor, SatisfiesClause]

/-- Soundness of reduction from NAE-SAT to 3-Coloring. -/
lemma NAEtoColorSoundness {V : Type} (f : NAESat3 V) :
  Is3Colorable (ReductionGraph f) → IsSatisfiable f := by
  intro ⟨⟨col, hcol⟩⟩
  simp only [SimpleGraph.top_adj] at hcol
  have colNe : ∀ {u v : OutputVertex V},
      u ≠ v → (EdgeRelation f u v ∨ EdgeRelation f v u) → col u ≠ col v :=
    fun hne hedge => hcol ⟨hne, hedge⟩
  -- Variables differ from ground
  have hVG : ∀ v : V, col (.varNode v) ≠ col .groundNode := fun v =>
    colNe (by simp) (Or.inl trivial)
  -- Clause nodes in same clause are pairwise distinct (triangle)
  have hCC : ∀ (c : NAEclause V), c ∈ f → ∀ (i j : Fin 3), i ≠ j →
      col (.clauseNode c i) ≠ col (.clauseNode c j) := fun c hcIn i j hij =>
    colNe (by simp [hij]) (Or.inl ⟨rfl, hcIn, hij⟩)
  -- Each clause node differs from its variable (using tactic to unfold EdgeRelation)
  have hVC0 : ∀ c : NAEclause V, col (.clauseNode c 0) ≠ col (.varNode c.v0) := fun c =>
    Ne.symm (colNe (by simp) (by left; left; exact ⟨rfl, rfl⟩))
  have hVC1 : ∀ c : NAEclause V, col (.clauseNode c 1) ≠ col (.varNode c.v1) := fun c =>
    Ne.symm (colNe (by simp) (by left; right; left; exact ⟨rfl, rfl⟩))
  have hVC2 : ∀ c : NAEclause V, col (.clauseNode c 2) ≠ col (.varNode c.v2) := fun c =>
    Ne.symm (colNe (by simp) (by left; right; right; exact ⟨rfl, rfl⟩))
  -- Define: True color = groundColor + 1 (mod 3); assign v = True iff varNode has that color
  let cTrue : Fin 3 := col .groundNode + 1
  let assign v := decide (col (.varNode v) = cTrue)
  refine ⟨assign, ?_⟩
  simp only [SatisfiesNAE3, List.all_eq_true]
  intro c hcIn
  by_contra hFalse
  -- NAE violated → all three variables have the same boolean assignment value
  have hSatF : SatisfiesClause assign c = false := by
    rcases Bool.eq_false_or_eq_true (SatisfiesClause assign c) with h | h
    · exact absurd h hFalse  -- h : ... = true, hFalse : ¬... = true → absurd
    · exact h                -- h : ... = false
  simp only [SatisfiesClause] at hSatF
  -- Extract: all three assign values are equal
  have hall : assign c.v0 = assign c.v1 ∧ assign c.v0 = assign c.v2 := by
    constructor <;>
      (cases h0 : assign c.v0 <;> cases h1 : assign c.v1 <;> cases h2 : assign c.v2 <;>
       simp_all)
  obtain ⟨h01, h02⟩ := hall
  -- In both cases (all true / all false), all three varNodes have the same Fin 3 color
  have hSameColor : col (.varNode c.v0) = col (.varNode c.v1) ∧
                    col (.varNode c.v0) = col (.varNode c.v2) := by
    cases hb : assign c.v0 with
    | true =>
      -- All true: all varNodes have color cTrue → directly equal
      have ht0 : col (.varNode c.v0) = cTrue := of_decide_eq_true hb
      have ht1 : col (.varNode c.v1) = cTrue := of_decide_eq_true (h01.symm.trans hb)
      have ht2 : col (.varNode c.v2) = cTrue := of_decide_eq_true (h02.symm.trans hb)
      exact ⟨ht0.trans ht1.symm, ht0.trans ht2.symm⟩
    | false =>
      -- All false: varNodes ≠ cTrue and ≠ ground → unique remaining color in Fin 3
      have hf0 : col (.varNode c.v0) ≠ cTrue := of_decide_eq_false hb
      have hf1 : col (.varNode c.v1) ≠ cTrue := of_decide_eq_false (h01.symm.trans hb)
      have hf2 : col (.varNode c.v2) ≠ cTrue := of_decide_eq_false (h02.symm.trans hb)
      have hg0 := hVG c.v0; have hg1 := hVG c.v1; have hg2 := hVG c.v2
      -- cTrue ≠ groundNode color (adding 1 in Fin 3 is always a change)
      have hcTneG : cTrue.val ≠ (col .groundNode).val := by
        intro heq
        have hlt := (col .groundNode).isLt
        have := Fin.val_add (col .groundNode) (1 : Fin 3)
        simp only [Fin.val_one] at this
        omega
      -- omega: three constraints (< 3, ≠ g, ≠ ct, ct ≠ g) uniquely pin the value
      constructor
      · apply Fin.ext
        have := (col .groundNode).isLt
        have := (col (.varNode c.v0)).isLt
        have := (col (.varNode c.v1)).isLt
        have := fun h => hg0 (Fin.ext h); have := fun h => hg1 (Fin.ext h)
        have := fun h => hf0 (Fin.ext h); have := fun h => hf1 (Fin.ext h)
        omega
      · apply Fin.ext
        have := (col .groundNode).isLt
        have := (col (.varNode c.v0)).isLt
        have := (col (.varNode c.v2)).isLt
        have := fun h => hg0 (Fin.ext h); have := fun h => hg2 (Fin.ext h)
        have := fun h => hf0 (Fin.ext h); have := fun h => hf2 (Fin.ext h)
        omega
  -- Now derive contradiction: 3 distinct clauseNode colors can't all avoid one var color
  obtain ⟨hcol01, hcol02⟩ := hSameColor
  have hVC0c := hVC0 c
  have hVC1c : col (.clauseNode c 1) ≠ col (.varNode c.v0) :=
    fun h => hVC1 c (h.trans hcol01)
  have hVC2c : col (.clauseNode c 2) ≠ col (.varNode c.v0) :=
    fun h => hVC2 c (h.trans hcol02)
  -- Three distinct Fin 3 values all ≠ x is impossible (pigeonhole)
  have cn0 := (col (.clauseNode c 0)).isLt
  have cn1 := (col (.clauseNode c 1)).isLt
  have cn2 := (col (.clauseNode c 2)).isLt
  have cvx := (col (.varNode c.v0)).isLt
  have ne01 : (col (.clauseNode c 0)).val ≠ (col (.clauseNode c 1)).val :=
    fun h => hCC c hcIn 0 1 (by decide) (Fin.ext h)
  have ne02 : (col (.clauseNode c 0)).val ≠ (col (.clauseNode c 2)).val :=
    fun h => hCC c hcIn 0 2 (by decide) (Fin.ext h)
  have ne12 : (col (.clauseNode c 1)).val ≠ (col (.clauseNode c 2)).val :=
    fun h => hCC c hcIn 1 2 (by decide) (Fin.ext h)
  have nex0 : (col (.clauseNode c 0)).val ≠ (col (.varNode c.v0)).val :=
    fun h => hVC0c (Fin.ext h)
  have nex1 : (col (.clauseNode c 1)).val ≠ (col (.varNode c.v0)).val :=
    fun h => hVC1c (Fin.ext h)
  have nex2 : (col (.clauseNode c 2)).val ≠ (col (.varNode c.v0)).val :=
    fun h => hVC2c (Fin.ext h)
  omega

/-- Main reduction theorem from NAE-SAT to 3-Coloring. -/
theorem NAEtoColorReduction {V : Type} (f : NAESat3 V) :
  IsSatisfiable f ↔ Is3Colorable (ReductionGraph f) :=
  Iff.intro (NAEtoColorCompleteness f) (NAEtoColorSoundness f)

end NAEtoColor
