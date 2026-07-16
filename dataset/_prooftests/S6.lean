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

abbrev Term (n : ℕ) := List (Literal n)

abbrev DNF (n : ℕ) := List (Term n)

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

namespace SwitchingLemma2
variable {n : ℕ}
private instance (n : ℕ) : Fintype (Restriction n) :=
  inferInstanceAs (Fintype (Fin n → Option Bool))
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

open BoolCircuit SwitchingLemma2 SwitchingBernoulli

open Classical in
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000

noncomputable section
namespace LMN
variable {n : ℕ}
def dedupTermVar (t : Term n) : Term n :=
  t.foldr (fun l acc =>
    if acc.any (fun l' => decide (l'.var = l.var)) then acc
    else l :: acc) []
end LMN
end

noncomputable section
namespace LMN
variable {n : ℕ}
def termHasContradiction (t : Term n) : Bool :=
  t.any (fun l₁ => t.any (fun l₂ => decide (l₁.var = l₂.var) && decide (l₁.neg ≠ l₂.neg)))
end LMN
end

noncomputable section
namespace LMN
variable {n : ℕ}
def cleanDNF (d : DNF n) : DNF n :=
  (d.filter (fun t => !termHasContradiction t)).map dedupTermVar
end LMN
end

noncomputable section
namespace LMN
variable {n : ℕ}
lemma dedupTermVar_nodup (t : Term n) : (dedupTermVar t).Nodup := by
  -- By induction on the list t, we can show that the foldr operation preserves the nodup property.
  have h_ind : ∀ (t : List (Literal n)) (acc : List (Literal n)), List.Nodup acc → List.Nodup (t.foldr (fun l acc => if acc.any (fun l' => decide (l'.var = l.var)) then acc else l :: acc) acc) := by
    intro t acc hacc; induction t <;> aesop;
  exact h_ind _ _ ( by simp +decide )
end LMN
end

noncomputable section
namespace LMN
variable {n : ℕ}
lemma cleanDNF_nodup (d : DNF n) :
    ∀ t ∈ cleanDNF d, t.Nodup := by
      intro t ht
      rw [cleanDNF] at ht
      rcases List.mem_map.mp ht with ⟨t₀, ht₀, rfl⟩
      apply dedupTermVar_nodup
end LMN
end
