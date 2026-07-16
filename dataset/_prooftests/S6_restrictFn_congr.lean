import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic
import Mathlib
import Mathlib.Tactic.Cases

namespace SwitchingLemmaCNF
end SwitchingLemmaCNF
namespace SwitchingLemma2
end SwitchingLemma2
namespace BoolCircuit
end BoolCircuit
namespace SwitchingBernoulli
end SwitchingBernoulli
namespace LMN
end LMN

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

def Literal.eval {n : ℕ} (l : Literal n) (x : Fin n → Bool) : Bool :=
  if l.neg then !x l.var else x l.var

inductive DecisionTree (n : ℕ) where
  | leaf   (val : Bool)                            : DecisionTree n
  | branch (var : Fin n) (lo hi : DecisionTree n) : DecisionTree n

def DecisionTree.eval {n : ℕ} : DecisionTree n → (Fin n → Bool) → Bool
  | .leaf b,          _  => b
  | .branch i lo hi,  x  => if x i then hi.eval x else lo.eval x

def DecisionTree.depth {n : ℕ} : DecisionTree n → ℕ
  | .leaf _          => 0
  | .branch _ lo hi  => 1 + max lo.depth hi.depth

open Classical

namespace SwitchingLemma2
variable {n : ℕ}
abbrev Restriction (n : ℕ) := Fin n → Option Bool
end SwitchingLemma2

namespace SwitchingLemma2.Restriction
variable {n : ℕ}
def extend {n : ℕ} (ρ : Restriction n) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => (ρ i).getD (x i)
end SwitchingLemma2.Restriction

namespace SwitchingLemma2
variable {n : ℕ}
def restrictFn {n : ℕ} (f : (Fin n → Bool) → Bool) (ρ : Restriction n) :
    (Fin n → Bool) → Bool :=
  fun x => f (ρ.extend x)
end SwitchingLemma2

open Classical

open Classical

def Literal.flipNeg {n : ℕ} (l : Literal n) : Literal n :=
  ⟨l.var, !l.neg⟩

@[simp]
lemma Literal.flipNeg_eval {n : ℕ} (l : Literal n) (x : Fin n → Bool) :
    l.flipNeg.eval x = !(l.eval x) := by
  simp only [Literal.flipNeg, Literal.eval]
  cases l.neg <;> simp

@[simp]
lemma Literal.flipNeg_var {n : ℕ} (l : Literal n) :
    l.flipNeg.var = l.var := rfl

def DecisionTree.negateLeaves {n : ℕ} : DecisionTree n → DecisionTree n
  | .leaf b => .leaf (!b)
  | .branch v lo hi => .branch v (negateLeaves lo) (negateLeaves hi)

@[simp]
lemma DecisionTree.negateLeaves_eval {n : ℕ} (T : DecisionTree n) (x : Fin n → Bool) :
    T.negateLeaves.eval x = !(T.eval x) := by
  induction T with
  | leaf b => simp [negateLeaves, DecisionTree.eval]
  | branch v lo hi ih_lo ih_hi =>
    simp only [negateLeaves, DecisionTree.eval]
    split <;> simp_all

@[simp]
lemma DecisionTree.negateLeaves_depth {n : ℕ} (T : DecisionTree n) :
    T.negateLeaves.depth = T.depth := by
  induction T with
  | leaf _ => simp [negateLeaves, DecisionTree.depth]
  | branch v lo hi ih_lo ih_hi =>
    simp [negateLeaves, DecisionTree.depth, ih_lo, ih_hi]

open SwitchingLemmaCNF
open SwitchingLemma2

open BoolCircuit SwitchingLemma2 SwitchingBernoulli LMN

open Classical in
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000

noncomputable section
namespace LMN
variable {n : ℕ}
lemma restrictFn_congr (f g : (Fin n → Bool) → Bool) (ρ : Restriction n)
    (h : ∀ x, f x = g x) :
    ∀ x, restrictFn f ρ x = restrictFn g ρ x := by
  unfold restrictFn; aesop;
end LMN
end
