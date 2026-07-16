import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic
import Mathlib.Tactic.Cases

set_option maxHeartbeats 800000

namespace BoolCircuit
structure Lit (n : Nat) where
  idx : Fin n
  sign : Bool
deriving DecidableEq, Repr, Hashable
end BoolCircuit

namespace BoolCircuit
@[simp]
def Lit.eval (l : Lit n) (x : Fin n → Bool) : Bool :=
  if l.sign then x l.idx else !x l.idx
end BoolCircuit

structure Literal (n : ℕ) where
  var : Fin n
  neg : Bool
  deriving DecidableEq

inductive DecisionTree (n : ℕ) where
  | leaf   (val : Bool)                            : DecisionTree n
  | branch (var : Fin n) (lo hi : DecisionTree n) : DecisionTree n

def DecisionTree.depth {n : ℕ} : DecisionTree n → ℕ
  | .leaf _          => 0
  | .branch _ lo hi  => 1 + max lo.depth hi.depth

def DecisionTree.deepPath {n : ℕ} : DecisionTree n → List (Fin n × Bool)
  | .leaf _ => []
  | .branch v lo hi =>
    if hi.depth ≥ lo.depth then
      (v, true) :: hi.deepPath
    else
      (v, false) :: lo.deepPath

open Classical

namespace SwitchingLemma2
variable {n : ℕ}
abbrev Restriction (n : ℕ) := Fin n → Option Bool
end SwitchingLemma2

namespace SwitchingLemma2.Restriction
variable {n : ℕ}
def freeVars {n : ℕ} (ρ : Restriction n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (ρ i).isNone)
end SwitchingLemma2.Restriction

open Classical

namespace SwitchingLemma2
variable {n : ℕ}
noncomputable def termSubTree {n : ℕ} :
    List (Literal n) → Restriction n →
    (Restriction n → DecisionTree n) → DecisionTree n
  | [], ρ, cont => cont ρ
  | l :: rest, ρ, cont =>
    if l.var ∈ ρ.freeVars then
      .branch l.var
        (termSubTree rest (Function.update ρ l.var (some false)) cont)
        (termSubTree rest (Function.update ρ l.var (some true)) cont)
    else
      termSubTree rest ρ cont
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma termSubTree_cons_free {n : ℕ}
    (l : Literal n) (rest : List (Literal n)) (ρ : Restriction n)
    (cont : Restriction n → DecisionTree n)
    (hfree : l.var ∈ ρ.freeVars) :
    termSubTree (l :: rest) ρ cont = .branch l.var
      (termSubTree rest (Function.update ρ l.var (some false)) cont)
      (termSubTree rest (Function.update ρ l.var (some true)) cont) := by
  simp [termSubTree, hfree]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma termSubTree_deepPath_head_free {n : ℕ}
    (l : Literal n) (rest : List (Literal n)) (ρ : Restriction n)
    (cont : Restriction n → DecisionTree n)
    (hfree : l.var ∈ ρ.freeVars) :
    ∃ b, (termSubTree (l :: rest) ρ cont).deepPath =
      (l.var, b) :: (termSubTree rest (Function.update ρ l.var (some b)) cont).deepPath := by
  rw [termSubTree_cons_free l rest ρ cont hfree]
  -- .branch l.var lo hi where:
  --   lo = termSubTree rest (update false) cont
  --   hi = termSubTree rest (update true) cont
  -- deepPath picks the deeper side (ties → true).
  simp only [DecisionTree.deepPath]
  split
  · -- hi.depth ≥ lo.depth: take true branch
    exact ⟨true, rfl⟩
  · -- hi.depth < lo.depth: take false branch
    exact ⟨false, rfl⟩
end SwitchingLemma2
