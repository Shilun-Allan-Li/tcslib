/-
Copyright (c) 2026 UC Berkeley CS 294. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CS 294-268 course staff (UC Berkeley, Spring 2026)
         Lecturer: Venkatesan Guruswami

This file was authored by the course instructors and TA as lecture material.
It is included here as supplementary context for the SAT → 3-SAT → Clique
reductions formalised in the companion files.
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
# 3-SAT to 3-Coloring Reduction

## Main results
- SATtoColorReduction: IsSatisfiable f ↔ Is3Colorable (ReductionGraph f)

## References
- Course material from CS 294-268 (UC Berkeley, Spring 2026), V. Guruswami
-/

/-!

# 3-SAT and 3-COLORING

## 3-SAT
The **3-SAT** problem asks: given a set of Boolean variables `x_1, ..., x_n` and
a set of clauses `C_1, ..., C_m`, where each clause is a disjunction of exactly
three literals (a variable or its negation), does there exist a Boolean assignment
that satisfies all clauses?

## Reduction from 3-SAT to 3-COLORING

Given a 3-SAT instance over variables `x_1, ..., x_n` and clauses `C_1, ..., C_m`,
we create an instance of 3-COLORING over the following vertices:
* A "palette" triangle with nodes `Base=0`, `True=1`, `False=2` (all pairwise connected).
* A "literal" node for each literal `x_i` and `¬x_i`.
* Six "clause gadget" nodes per clause that encode the OR constraint.

The edges are:
* All palette nodes are pairwise connected (triangle fixing color semantics).
* `Base` is connected to every literal node.
* `pos(x)` is connected to `neg(x)` (forcing them to get opposite truth colors).
* Internal clause gadget edges (nodes 0–2 and 3–5 form triangles) plus
  connections to the clause's three literals.
* Gadget node 5 is connected to `Base` and `False`, forcing it to receive color
  `True` whenever the clause is satisfied.

**Proof Sketch.**

_Completeness (SAT → Colorable):_
Given a satisfying assignment, color the palette nodes by their index, literal
nodes by their truth value, and clause gadgets by `clauseGadgetColor`. The
definition of `clauseGadgetColor` guarantees node 5 gets color T=1, and all
gadget internal edges get distinct colors.

_Soundness (Colorable → SAT):_
Given a valid 3-coloring, define `assign v := (col(pos v) = col(palette 1))`.
If some clause had all three literals false under this assignment, all three
literal nodes would have the same color (≠ T, ≠ Base), which forces a
contradiction via the gadget's internal edge structure (omega on Fin 3 values).
-/

namespace SATtoColor

inductive Literal (V : Type)
| pos (v : V)
| neg (v : V)

structure Clause (V : Type) where
  l1 : Literal V
  l2 : Literal V
  l3 : Literal V

def SatisfiesLiteral {V : Type} (assign : V → Bool) : Literal V → Bool
  | Literal.pos v => assign v
  | Literal.neg v => !(assign v)

def SatisfiesClause {V : Type} (assign : V → Bool) (c : Clause V) : Bool :=
  SatisfiesLiteral assign c.l1 || SatisfiesLiteral assign c.l2 || SatisfiesLiteral assign c.l3

abbrev Sat3 (V : Type) := List (Clause V)

def SatisfiesSat3 {V : Type} (assign : V → Bool) (f : Sat3 V) : Bool :=
  f.all (SatisfiesClause assign)

noncomputable def IsSatisfiable {V : Type} (f : Sat3 V) : Prop :=
  ∃ (assign : V → Bool), SatisfiesSat3 assign f = true

-- Some examples to test definitions:
namespace SAT3_Example

def sat3_inst : Sat3 (Fin 4) := [
  ⟨Literal.pos 0, Literal.neg 1, Literal.neg 2⟩,
  ⟨Literal.neg 0, Literal.pos 1, Literal.neg 2⟩,
  ⟨Literal.neg 0, Literal.neg 1, Literal.neg 3⟩
]

def ex_assign_1 := ![true, true, false, false]

#eval SatisfiesClause ex_assign_1 sat3_inst[2]
#eval SatisfiesSat3 ex_assign_1 sat3_inst

example : IsSatisfiable sat3_inst := ⟨ex_assign_1, rfl⟩

end SAT3_Example

/-- Vertex set for reduction from 3-SAT to 3-COLORING.
• palette     – the special triangle fixing color semantics (Base=0, T=1, F=2).
• literalNode – one node per literal (pos and neg are separate nodes).
• clauseGadget – six internal nodes per clause encoding the OR constraint.
-/
inductive OutputVertex (V : Type)
| palette (p : Fin 3)
| literalNode (l : Literal V)
| clauseGadget (c : Clause V) (idx : Fin 6)

/-- A simple graph is 3-colorable if there exists a valid 3-coloring. -/
def Is3Colorable {V' : Type} (G : SimpleGraph V') : Prop :=
  Nonempty (G.Coloring (Fin 3))

/-- Edge relation for reduction from 3-SAT to 3-COLORING. -/
def EdgeRelation {V : Type} (clauses : Sat3 V) (u v: OutputVertex V) : Prop :=
  match u, v with
  | .palette i, .palette j => i ≠ j
  | .palette 0, .literalNode _ => True
  | .literalNode _, .palette 0 => True
  | .literalNode (.pos x), .literalNode (.neg y) => x = y
  | .literalNode (.neg x), .literalNode (.pos y) => x = y
  | .clauseGadget c1 i, .clauseGadget c2 j =>
      c1 = c2 ∧ c1 ∈ clauses ∧ (
        (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨
        (i = 3 ∧ j = 4) ∨ (i = 3 ∧ j = 5) ∨ (i = 4 ∧ j = 5) ∨
        (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 2) ∨
        (i = 4 ∧ j = 3) ∨ (i = 5 ∧ j = 3) ∨ (i = 5 ∧ j = 4)
      )
  | .literalNode z, .clauseGadget c i =>
      ((z = c.l1 ∧ i = 0) ∨ (z = c.l2 ∧ i = 1) ∨ (z = c.l3 ∧ i = 4))
  | .clauseGadget c i, .literalNode z =>
      ((z = c.l1 ∧ i = 0) ∨ (z = c.l2 ∧ i = 1) ∨ (z = c.l3 ∧ i = 4))
  | .clauseGadget _ 5, .palette 0 => True
  | .palette 0, .clauseGadget _ 5 => True
  | .clauseGadget _ 5, .palette 2 => True
  | .palette 2, .clauseGadget _ 5 => True
  | _, _ => False

/-- Simple graph for reduction from 3-SAT to 3-Coloring. -/
def ReductionGraph {V : Type} (f : Sat3 V) : SimpleGraph (OutputVertex V) where
  Adj u v := u ≠ v ∧ (EdgeRelation f u v ∨ EdgeRelation f v u)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless := fun _ h => h.1 rfl

/-- Coloring of clause gadget nodes given the boolean values of the three literals. -/
private def clauseGadgetColor (a b c3 : Bool) (k : Fin 6) : Fin 3 :=
  let ff3 := !a && !b && !c3
  let ff  := !a && !b
  match k with
  | ⟨5, _⟩ => 1
  | ⟨4, _⟩ => if ff3 then 0 else if ff then 2 else 0
  | ⟨3, _⟩ => if ff3 then 0 else if ff then 0 else 2
  | ⟨2, _⟩ => if ff3 then 0 else if ff then 2 else 1
  | ⟨1, _⟩ => if ff3 then 0 else if ff then 1 else if !b then 0 else 2
  | ⟨0, _⟩ => if ff3 then 0 else if ff then 0 else if !a then 0 else if !b then 2 else 0

/-- Coloring constructed from a satisfying assignment. -/
private def sat3Coloring {V : Type} (assign : V → Bool) : OutputVertex V → Fin 3
  | .palette p => p
  | .literalNode (.pos v) => if assign v then 1 else 2
  | .literalNode (.neg v) => if assign v then 2 else 1
  | .clauseGadget c k =>
      clauseGadgetColor (SatisfiesLiteral assign c.l1)
                        (SatisfiesLiteral assign c.l2)
                        (SatisfiesLiteral assign c.l3) k

private lemma sat3Coloring_litNode {V : Type} (assign : V → Bool) (l : Literal V) :
    sat3Coloring assign (.literalNode l) = if SatisfiesLiteral assign l then 1 else 2 := by
  match l with
  | .pos v => simp [sat3Coloring, SatisfiesLiteral]
  | .neg v =>
    show (if assign v then (2 : Fin 3) else 1) = if !assign v then 1 else 2
    match assign v with | true => rfl | false => rfl

/-- Completeness of reduction from 3-SAT to 3-Coloring. -/
lemma SATtoColorCompleteness {V : Type} (f : Sat3 V) :
  IsSatisfiable f → Is3Colorable (ReductionGraph f) := by
  intro ⟨assign, hsat⟩
  refine ⟨⟨sat3Coloring assign, ?_⟩⟩
  intro u v hadj
  simp only [SimpleGraph.top_adj]
  obtain ⟨hne, hedge⟩ := hadj
  suffices key : ∀ {a b : OutputVertex V}, EdgeRelation f a b →
                   sat3Coloring assign a ≠ sat3Coloring assign b by
    rcases hedge with h | h
    · exact key h
    · exact fun heq => key h heq.symm
  intro a b h
  cases a with
  | palette i =>
    cases b with
    | palette j =>
      simp only [sat3Coloring]
      simp only [EdgeRelation] at h
      exact h
    | literalNode l =>
      fin_cases i
      · rw [sat3Coloring_litNode]; simp only [sat3Coloring]
        cases SatisfiesLiteral assign l <;> simp
      · exact absurd h (by simp [EdgeRelation])
      · exact absurd h (by simp [EdgeRelation])
    | clauseGadget c k =>
      fin_cases i <;> fin_cases k <;>
        simp_all [EdgeRelation, sat3Coloring, clauseGadgetColor]
  | literalNode l =>
    cases b with
    | palette j =>
      fin_cases j
      · rw [sat3Coloring_litNode]; simp only [sat3Coloring]
        cases SatisfiesLiteral assign l <;> simp
      · exact absurd h (by simp [EdgeRelation])
      · exact absurd h (by simp [EdgeRelation])
    | literalNode l2 =>
      cases l with
      | pos x =>
        cases l2 with
        | pos y => exact absurd h (by simp [EdgeRelation])
        | neg y =>
          simp only [EdgeRelation] at h
          simp only [sat3Coloring]; subst h
          cases assign x <;> simp
      | neg x =>
        cases l2 with
        | neg y => exact absurd h (by simp [EdgeRelation])
        | pos y =>
          simp only [EdgeRelation] at h
          simp only [sat3Coloring]; subst h
          cases assign x <;> simp
    | clauseGadget c k =>
      simp only [EdgeRelation] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals (
        rw [sat3Coloring_litNode]; simp only [sat3Coloring]
        cases hA : SatisfiesLiteral assign c.l1 <;>
        cases hB : SatisfiesLiteral assign c.l2 <;>
        cases hC : SatisfiesLiteral assign c.l3 <;>
        simp [clauseGadgetColor])
  | clauseGadget c k =>
    cases b with
    | palette j =>
      fin_cases j <;> fin_cases k <;>
        simp_all [EdgeRelation, sat3Coloring, clauseGadgetColor]
    | literalNode l =>
      simp only [EdgeRelation] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals (
        rw [sat3Coloring_litNode]; simp only [sat3Coloring]
        cases hA : SatisfiesLiteral assign c.l1 <;>
        cases hB : SatisfiesLiteral assign c.l2 <;>
        cases hC : SatisfiesLiteral assign c.l3 <;>
        simp [clauseGadgetColor])
    | clauseGadget c2 j =>
      simp only [EdgeRelation] at h
      obtain ⟨rfl, hcIn, hidx⟩ := h
      simp only [sat3Coloring]
      have hClauseTrue : SatisfiesClause assign c = true :=
        List.all_eq_true.mp hsat c hcIn
      rcases hidx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                       ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                       ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                       ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals (
        cases hA : SatisfiesLiteral assign c.l1 <;>
        cases hB : SatisfiesLiteral assign c.l2 <;>
        cases hC : SatisfiesLiteral assign c.l3 <;>
        simp_all [clauseGadgetColor, SatisfiesClause])

/-- Soundness of reduction from 3-SAT to 3-Coloring. -/
lemma SATtoColorSoundness {V : Type} (f : Sat3 V) :
  Is3Colorable (ReductionGraph f) → IsSatisfiable f := by
  intro ⟨⟨col, hcol⟩⟩
  simp only [SimpleGraph.top_adj] at hcol
  have colNe : ∀ {u v : OutputVertex V},
      u ≠ v → (EdgeRelation f u v ∨ EdgeRelation f v u) → col u ≠ col v :=
    fun hne hedge => hcol ⟨hne, hedge⟩
  have hP01 : col (.palette 0) ≠ col (.palette 1) := colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hP02 : col (.palette 0) ≠ col (.palette 2) := colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hP12 : col (.palette 1) ≠ col (.palette 2) := colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hLB : ∀ l : Literal V, col (.literalNode l) ≠ col (.palette 0) := fun l =>
    colNe (by simp) (Or.inr trivial)
  have hPN : ∀ x : V, col (.literalNode (.pos x)) ≠ col (.literalNode (.neg x)) := fun x =>
    colNe (by simp) (Or.inl rfl)
  have hG5B : ∀ c' : Clause V, col (.clauseGadget c' 5) ≠ col (.palette 0) := fun c' =>
    colNe (by simp) (Or.inl trivial)
  have hG5F : ∀ c' : Clause V, col (.clauseGadget c' 5) ≠ col (.palette 2) := fun c' =>
    colNe (by simp) (Or.inl trivial)
  let assign := fun v : V => decide (col (.literalNode (.pos v)) = col (.palette 1))
  have hLFT : ∀ l : Literal V, SatisfiesLiteral assign l = false →
      col (.literalNode l) ≠ col (.palette 1) := by
    intro l hl
    cases l with
    | pos v =>
      simp only [SatisfiesLiteral] at hl
      exact of_decide_eq_false hl
    | neg v =>
      simp only [SatisfiesLiteral] at hl
      have hav : col (.literalNode (.pos v)) = col (.palette 1) := by
        apply of_decide_eq_true
        cases h : assign v
        · exfalso; simp [h] at hl
        · exact h
      intro hcontra
      exact hPN v (hav.trans hcontra.symm)
  refine ⟨assign, ?_⟩
  simp only [SatisfiesSat3, List.all_eq_true]
  intro c hcIn
  by_contra hFalse
  have hSatF : SatisfiesClause assign c = false := by
    cases h : SatisfiesClause assign c with
    | true => exact absurd h hFalse
    | false => rfl
  simp only [SatisfiesClause] at hSatF
  have hl1F : SatisfiesLiteral assign c.l1 = false := by
    cases h : SatisfiesLiteral assign c.l1 <;> simp_all
  have hl2F : SatisfiesLiteral assign c.l2 = false := by
    cases h : SatisfiesLiteral assign c.l2 <;> simp_all
  have hl3F : SatisfiesLiteral assign c.l3 = false := by
    cases h : SatisfiesLiteral assign c.l3 <;> simp_all
  have hL1neT := hLFT c.l1 hl1F
  have hL2neT := hLFT c.l2 hl2F
  have hL3neT := hLFT c.l3 hl3F
  have hG5T : col (.clauseGadget c 5) = col (.palette 1) := by
    apply Fin.ext
    have i0 := (col (.clauseGadget c 5)).isLt
    have i1 := (col (.palette 0)).isLt
    have i2 := (col (.palette 1)).isLt
    have i3 := (col (.palette 2)).isLt
    have h1 : (col (.clauseGadget c 5)).val ≠ (col (.palette 0)).val := fun h => hG5B c (Fin.ext h)
    have h2 : (col (.clauseGadget c 5)).val ≠ (col (.palette 2)).val := fun h => hG5F c (Fin.ext h)
    have h3 : (col (.palette 0)).val ≠ (col (.palette 1)).val := fun h => hP01 (Fin.ext h)
    have h4 : (col (.palette 0)).val ≠ (col (.palette 2)).val := fun h => hP02 (Fin.ext h)
    have h5 : (col (.palette 1)).val ≠ (col (.palette 2)).val := fun h => hP12 (Fin.ext h)
    omega
  have hG01 : col (.clauseGadget c 0) ≠ col (.clauseGadget c 1) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inl ⟨rfl, rfl⟩⟩)
  have hG02 : col (.clauseGadget c 0) ≠ col (.clauseGadget c 2) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
  have hG12 : col (.clauseGadget c 1) ≠ col (.clauseGadget c 2) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)
  have hG23 : col (.clauseGadget c 2) ≠ col (.clauseGadget c 3) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩)
  have hG34 : col (.clauseGadget c 3) ≠ col (.clauseGadget c 4) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)
  have hG35 : col (.clauseGadget c 3) ≠ col (.clauseGadget c 5) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩)
  have hG45 : col (.clauseGadget c 4) ≠ col (.clauseGadget c 5) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))⟩)
  have hL1G0 : col (.literalNode c.l1) ≠ col (.clauseGadget c 0) :=
    colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hL2G1 : col (.literalNode c.l2) ≠ col (.clauseGadget c 1) :=
    colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hL3G4 : col (.literalNode c.l3) ≠ col (.clauseGadget c 4) :=
    colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have vp0 := (col (.palette 0)).isLt;       have vp1 := (col (.palette 1)).isLt
  have vp2 := (col (.palette 2)).isLt
  have vg0 := (col (.clauseGadget c 0)).isLt; have vg1 := (col (.clauseGadget c 1)).isLt
  have vg2 := (col (.clauseGadget c 2)).isLt; have vg3 := (col (.clauseGadget c 3)).isLt
  have vg4 := (col (.clauseGadget c 4)).isLt; have vg5 := (col (.clauseGadget c 5)).isLt
  have vl1 := (col (.literalNode c.l1)).isLt; have vl2 := (col (.literalNode c.l2)).isLt
  have vl3 := (col (.literalNode c.l3)).isLt
  have hp01 : (col (.palette 0)).val ≠ (col (.palette 1)).val := fun h => hP01 (Fin.ext h)
  have hp02 : (col (.palette 0)).val ≠ (col (.palette 2)).val := fun h => hP02 (Fin.ext h)
  have hp12 : (col (.palette 1)).val ≠ (col (.palette 2)).val := fun h => hP12 (Fin.ext h)
  have hl1b : (col (.literalNode c.l1)).val ≠ (col (.palette 0)).val := fun h => hLB c.l1 (Fin.ext h)
  have hl2b : (col (.literalNode c.l2)).val ≠ (col (.palette 0)).val := fun h => hLB c.l2 (Fin.ext h)
  have hl3b : (col (.literalNode c.l3)).val ≠ (col (.palette 0)).val := fun h => hLB c.l3 (Fin.ext h)
  have hl1t : (col (.literalNode c.l1)).val ≠ (col (.palette 1)).val := fun h => hL1neT (Fin.ext h)
  have hl2t : (col (.literalNode c.l2)).val ≠ (col (.palette 1)).val := fun h => hL2neT (Fin.ext h)
  have hl3t : (col (.literalNode c.l3)).val ≠ (col (.palette 1)).val := fun h => hL3neT (Fin.ext h)
  have hl1g0 : (col (.literalNode c.l1)).val ≠ (col (.clauseGadget c 0)).val := fun h => hL1G0 (Fin.ext h)
  have hl2g1 : (col (.literalNode c.l2)).val ≠ (col (.clauseGadget c 1)).val := fun h => hL2G1 (Fin.ext h)
  have hl3g4 : (col (.literalNode c.l3)).val ≠ (col (.clauseGadget c 4)).val := fun h => hL3G4 (Fin.ext h)
  have hg01 : (col (.clauseGadget c 0)).val ≠ (col (.clauseGadget c 1)).val := fun h => hG01 (Fin.ext h)
  have hg02 : (col (.clauseGadget c 0)).val ≠ (col (.clauseGadget c 2)).val := fun h => hG02 (Fin.ext h)
  have hg12 : (col (.clauseGadget c 1)).val ≠ (col (.clauseGadget c 2)).val := fun h => hG12 (Fin.ext h)
  have hg23 : (col (.clauseGadget c 2)).val ≠ (col (.clauseGadget c 3)).val := fun h => hG23 (Fin.ext h)
  have hg34 : (col (.clauseGadget c 3)).val ≠ (col (.clauseGadget c 4)).val := fun h => hG34 (Fin.ext h)
  have hg35 : (col (.clauseGadget c 3)).val ≠ (col (.clauseGadget c 5)).val := fun h => hG35 (Fin.ext h)
  have hg45 : (col (.clauseGadget c 4)).val ≠ (col (.clauseGadget c 5)).val := fun h => hG45 (Fin.ext h)
  have hg5t : (col (.clauseGadget c 5)).val = (col (.palette 1)).val := congrArg Fin.val hG5T
  omega

/-- Main theorem: 3-SAT is satisfiable iff the reduction graph is 3-colorable. -/
theorem SATtoColorReduction {V : Type} (f : Sat3 V) :
  IsSatisfiable f ↔ Is3Colorable (ReductionGraph f) :=
  Iff.intro (SATtoColorCompleteness f) (SATtoColorSoundness f)

end SATtoColor
