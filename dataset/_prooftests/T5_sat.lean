import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace SATtoColor
inductive Literal (V : Type)
| pos (v : V)
| neg (v : V)
end SATtoColor

namespace SATtoColor
structure Clause (V : Type) where
  l1 : Literal V
  l2 : Literal V
  l3 : Literal V
end SATtoColor

namespace SATtoColor
def SatisfiesLiteral {V : Type} (assign : V → Bool) : Literal V → Bool
  | Literal.pos v => assign v
  | Literal.neg v => !(assign v)
end SATtoColor

namespace SATtoColor
def SatisfiesClause {V : Type} (assign : V → Bool) (c : Clause V) : Bool :=
  SatisfiesLiteral assign c.l1 || SatisfiesLiteral assign c.l2 || SatisfiesLiteral assign c.l3
end SATtoColor

namespace SATtoColor
abbrev Sat3 (V : Type) := List (Clause V)
end SATtoColor

namespace SATtoColor
def SatisfiesSat3 {V : Type} (assign : V → Bool) (f : Sat3 V) : Bool :=
  f.all (SatisfiesClause assign)
end SATtoColor

namespace SATtoColor
noncomputable def IsSatisfiable {V : Type} (f : Sat3 V) : Prop :=
  ∃ (assign : V → Bool), SatisfiesSat3 assign f = true
end SATtoColor

namespace SATtoColor
inductive OutputVertex (V : Type)
| palette (p : Fin 3)
| literalNode (l : Literal V)
| clauseGadget (c : Clause V) (idx : Fin 6)
end SATtoColor

namespace SATtoColor
def Is3Colorable {V' : Type} (G : SimpleGraph V') : Prop :=
  Nonempty (G.Coloring (Fin 3))
end SATtoColor

namespace SATtoColor
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
end SATtoColor

namespace SATtoColor
def ReductionGraph {V : Type} (f : Sat3 V) : SimpleGraph (OutputVertex V) where
  Adj u v := u ≠ v ∧ (EdgeRelation f u v ∨ EdgeRelation f v u)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless := fun _ h => h.1 rfl
end SATtoColor

namespace SATtoColor
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
end SATtoColor

namespace SATtoColor
private def sat3Coloring {V : Type} (assign : V → Bool) : OutputVertex V → Fin 3
  | .palette p => p
  | .literalNode (.pos v) => if assign v then 1 else 2
  | .literalNode (.neg v) => if assign v then 2 else 1
  | .clauseGadget c k =>
      clauseGadgetColor (SatisfiesLiteral assign c.l1)
                        (SatisfiesLiteral assign c.l2)
                        (SatisfiesLiteral assign c.l3) k
end SATtoColor

namespace SATtoColor
private lemma sat3Coloring_litNode {V : Type} (assign : V → Bool) (l : Literal V) :
    sat3Coloring assign (.literalNode l) = if SatisfiesLiteral assign l then 1 else 2 := by
  match l with
  | .pos v => simp [sat3Coloring, SatisfiesLiteral]
  | .neg v =>
    show (if assign v then (2 : Fin 3) else 1) = if !assign v then 1 else 2
    match assign v with | true => rfl | false => rfl
end SATtoColor

namespace SATtoColor
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
end SATtoColor
