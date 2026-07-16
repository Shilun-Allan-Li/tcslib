import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic
import Mathlib
import Mathlib.Tactic.Cases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.SymmDiff
import Mathlib.Probability.Moments.Basic

namespace SwitchingLemmaCNF
end SwitchingLemmaCNF
namespace SwitchingLemma2
end SwitchingLemma2
namespace BoolCircuit
end BoolCircuit

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

open BoolCircuit

set_option maxHeartbeats 400000

noncomputable section
namespace LMN
variable {n : ℕ}
def mergeGates {α : Type*} {m₁ m₂ : ℕ}
    (g₁ : Fin m₁ → α) (g₂ : Fin m₂ → α) : Fin (m₁ + m₂) → α :=
  fun j => if h : j.val < m₁ then g₁ ⟨j.val, h⟩ else g₂ ⟨j.val - m₁, by omega⟩
end LMN
end

noncomputable section
namespace LMN
variable {n : ℕ}
@[simp]
lemma mergeGates_castAdd {α : Type*} {m₁ m₂ : ℕ}
    (g₁ : Fin m₁ → α) (g₂ : Fin m₂ → α) (i : Fin m₁) :
    mergeGates g₁ g₂ (Fin.castAdd m₂ i) = g₁ i := by
  unfold mergeGates
  simp [i.isLt]
end LMN
end

noncomputable section
namespace LMN
variable {n : ℕ}
@[simp]
lemma mergeGates_natAdd {α : Type*} {m₁ m₂ : ℕ}
    (g₁ : Fin m₁ → α) (g₂ : Fin m₂ → α) (i : Fin m₂) :
    mergeGates g₁ g₂ (Fin.natAdd m₁ i) = g₂ i := by
  unfold mergeGates
  have : ¬ (m₁ + i.val < m₁) := by omega
  simp [this]
end LMN
end

set_option maxHeartbeats 400000

open scoped BigOperators

namespace BooleanAnalysis
abbrev BoolCube (n : ℕ) := Fin n → Bool
end BooleanAnalysis

namespace BooleanAnalysis
abbrev BooleanFunc (n : ℕ) := BoolCube n → ℝ
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
noncomputable def uniformWeight (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
noncomputable def expect (f : BooleanFunc n) : ℝ :=
  uniformWeight n * ∑ x : BoolCube n, f x
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
noncomputable def innerProduct (f g : BooleanFunc n) : ℝ :=
  expect (fun x ↦ f x * g x)
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
def boolToSign (b : Bool) : ℝ := if b then -1 else 1
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
@[simp]
lemma boolToSign_false : boolToSign false = 1 := rfl
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
@[simp]
lemma boolToSign_true : boolToSign true = -1 := rfl
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
@[simp]
lemma boolToSign_sq (b : Bool) : boolToSign b ^ 2 = 1 := by
  cases b <;> simp [boolToSign]
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
@[simp]
lemma boolToSign_mul_self (b : Bool) : boolToSign b * boolToSign b = 1 := by
  cases b <;> simp [boolToSign]
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
noncomputable def chiS (S : Finset (Fin n)) : BooleanFunc n :=
  fun x ↦ ∏ i ∈ S, boolToSign (x i)
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
@[simp]
lemma chiS_empty : χ_[(∅ : Finset (Fin n))] = fun _ ↦ 1 := by
  ext x; simp [chiS]
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
@[simp]
lemma chiS_singleton (i : Fin n) (x : BoolCube n) :
    χ_[{i}] x = boolToSign (x i) := by
  simp [chiS]
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
lemma chiS_mul_chiS (S T : Finset (Fin n)) (x : BoolCube n) :
    χ_[S] x * χ_[T] x = χ_[symmDiff S T] x := by
  simp only [chiS]
  -- Decompose: S = (S \ T) ∪ (S ∩ T), T = (T \ S) ∪ (T ∩ S)
  have hS : ∏ i ∈ S, boolToSign (x i) =
      (∏ i ∈ S \ T, boolToSign (x i)) * ∏ i ∈ S ∩ T, boolToSign (x i) := by
    conv_lhs => rw [← Finset.sdiff_union_inter S T]
    apply Finset.prod_union
    simp only [Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_inter, not_and]
    tauto
  have hT : ∏ i ∈ T, boolToSign (x i) =
      (∏ i ∈ T \ S, boolToSign (x i)) * ∏ i ∈ S ∩ T, boolToSign (x i) := by
    conv_lhs => rw [← Finset.sdiff_union_inter T S]
    rw [Finset.inter_comm T S]
    apply Finset.prod_union
    simp only [Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_inter, not_and]
    tauto
  -- The intersection product squares to 1
  have hcancel : (∏ i ∈ S ∩ T, boolToSign (x i)) * ∏ i ∈ S ∩ T, boolToSign (x i) = 1 := by
    rw [← Finset.prod_mul_distrib]; simp [boolToSign_mul_self]
  rw [hS, hT, symmDiff_def, Finset.sup_eq_union, Finset.prod_union disjoint_sdiff_sdiff]
  -- Goal: (A * P) * (B * P) = A * B  where P² = 1
  set P := ∏ i ∈ S ∩ T, boolToSign (x i)
  set A := ∏ i ∈ S \ T, boolToSign (x i)
  set B := ∏ i ∈ T \ S, boolToSign (x i)
  calc A * P * (B * P) = A * B * (P * P) := by ring
    _ = A * B * 1 := by rw [hcancel]
    _ = A * B := by ring
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
@[simp]
private lemma sum_boolToSign : ∑ b : Bool, boolToSign b = 0 := by
  simp [boolToSign]
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
private lemma sum_chiS (S : Finset (Fin n)) :
    ∑ x : BoolCube n, chiS S x = if S = ∅ then 2 ^ n else 0 := by
  simp only [chiS]
  by_cases hS : S = ∅
  · subst hS; simp [Fintype.card_pi, Fintype.card_bool]
  · simp only [hS, if_false]
    have factored : ∑ x : BoolCube n, ∏ i ∈ S, boolToSign (x i) =
        ∑ x : BoolCube n, ∏ i : Fin n, (if i ∈ S then boolToSign (x i) else 1) := by
      congr 1; ext x; rw [← Finset.prod_filter]; simp
    rw [factored]
    -- Goal: ∑ x : BoolCube n, ∏ i : Fin n, g i (x i) = 0
    -- where g i b = if i ∈ S then boolToSign b else 1
    -- Factor: = ∏ i : Fin n, ∑ b : Bool, g i b  (by Fintype.prod_sum reversed)
    rw [show ∑ x : BoolCube n, ∏ i : Fin n, (if i ∈ S then boolToSign (x i) else 1) =
        ∏ i : Fin n, ∑ b : Bool, (if i ∈ S then boolToSign b else 1) from
      (Fintype.prod_sum (fun i b => if i ∈ S then boolToSign b else 1)).symm]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
theorem fourier_coeff_chi (S T : Finset (Fin n)) :
    innerProduct (chiS S) (chiS T) = if S = T then 1 else 0 := by
  simp only [innerProduct, expect, uniformWeight]
  have step : ∑ x : BoolCube n, chiS S x * chiS T x =
      ∑ x : BoolCube n, chiS (symmDiff S T) x := by
    congr 1; ext x; exact chiS_mul_chiS S T x
  rw [step, sum_chiS]
  by_cases hst : S = T
  · -- S = T: symmDiff S T = ∅
    subst hst
    simp only [symmDiff_self, Finset.bot_eq_empty, ↓reduceIte]
    rw [← mul_pow]; norm_num
  · -- S ≠ T: symmDiff S T ≠ ∅
    have hd : symmDiff S T ≠ ∅ := by
      intro h
      apply hst
      have : symmDiff S T = ⊥ := by rwa [Finset.bot_eq_empty]
      exact symmDiff_eq_bot.mp this
    simp [hd, hst]
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
@[simp]
lemma innerProduct_chi_self (S : Finset (Fin n)) :
    innerProduct (chiS S) (chiS S) = 1 := by
  simp [fourier_coeff_chi]
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
def flipBit (x : BoolCube n) (i : Fin n) : BoolCube n :=
  Function.update x i (!x i)
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
@[simp]
lemma flipBit_flipBit (x : BoolCube n) (i : Fin n) : flipBit (flipBit x i) i = x := by
  ext j
  simp [flipBit, Function.update]
  split_ifs with h
  · subst h; simp
  · rfl
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
@[simp]
lemma boolToSign_not (b : Bool) : boolToSign (!b) = -boolToSign b := by
  cases b <;> simp [boolToSign]
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
lemma chiS_neg (S : Finset (Fin n)) (x : BoolCube n) :
    chiS S (fun i => !x i) = (-1 : ℝ) ^ S.card * chiS S x := by
  simp only [chiS]
  simp_rw [boolToSign_not]
  -- ∏_{i∈S} (-boolToSign (x i)) = (-1)^|S| * ∏_{i∈S} boolToSign (x i)
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Finset.prod_insert ha, ih]
    ring
end BooleanAnalysis
