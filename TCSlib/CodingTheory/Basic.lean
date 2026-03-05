import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finmap
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Disjoint

/-!
# Coding Theory — Core Definitions

This file provides the foundational definitions for coding theory over a finite
alphabet `α`.

## Main Definitions

* `Codeword n α` : a vector of length `n` over alphabet `α`, i.e. `Fin n → α`.
* `Code n α` : a code of block-length `n` over `α`, i.e. a `Finset (Codeword n α)`.
* `Linear_Code C G` : predicate asserting that `C` is the image of the linear map given
  by generator matrix `G`.
* `Linear_Code' C m` : existential variant — `C` is the image of *some* `n×m` generator matrix.
* `qaryEntropy q p` : the q-ary entropy function `H_q(p)`.
* `hamming_distance c₁ c₂` : Hamming distance between two codewords.
* `distance C d` : predicate asserting that `d` is the minimum distance of code `C`.
* `rate C` : the rate of code `C` (base-`|α|` logarithm of `|C|` over block length).
* `weight c` : Hamming weight of a codeword `c`.
* `hamming_ball l c` : the Hamming ball of radius `l` centred at `c`.

## Main Results

* `dist_le_length` : the minimum distance of a code is at most its block length.

-/

set_option linter.unusedSectionVars false

open Set Filter Asymptotics Finset

namespace CodingTheory

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α]
variable {n k : ℕ}

/-- A codeword of block-length `n` over alphabet `α`.  Concretely, a function `Fin n → α`. -/
abbrev Codeword (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] := (i : Fin n) → α

namespace Codeword

/-- Pointwise addition of two codewords. -/
@[simp]
def add (c₁ c₂ : Codeword n α) : Codeword n α := fun i ↦ (c₁ i + c₂ i)

/-- Pointwise subtraction of two codewords. -/
@[simp]
def sub (c₁ c₂ : Codeword n α) : Codeword n α := fun i ↦ (c₁ i - c₂ i)

/-- The all-zeros codeword. -/
@[simp]
def zero : Codeword n α := fun (_ : Fin n) ↦ 0

/-- A code of block-length `n` over `α`: a finite set of codewords. -/
abbrev Code (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] := Finset (Codeword n α)

/-- A code `C` is *linear* with generator matrix `G : Fin n × Fin m → α` if `C` is
    exactly the image of the linear map `G · -`. -/
def Linear_Code (C : Code n α) (G : Matrix (Fin n) (Fin m) α) :=
  (∀ c' : Codeword m α, Matrix.mulVec G c' ∈ C) ∧
  (∀ c ∈ C, ∃ c' : Codeword m α, c = Matrix.mulVec G c')

/-- Existential variant of `Linear_Code`: `C` is the image of *some* `n×m` generator matrix. -/
def Linear_Code' (C : Code n α) (m : ℕ) :=
  ∃ (G : Matrix (Fin n) (Fin m) α),
    (∀ c' : Codeword m α, Matrix.mulVec G c' ∈ C) ∧
    (∀ c ∈ C, ∃ c' : Codeword m α, c = Matrix.mulVec G c')

/-- The q-ary entropy function `H_q(p) = p·log_q(q-1) - p·log_q(p) - (1-p)·log_q(1-p)`. -/
noncomputable def qaryEntropy (q : ℕ) (p : ℝ) :=
  p * (Real.logb q (q-1)) - p * (Real.logb q p) - (1-p)*(Real.logb q (1 -p))

/-- The Hamming distance between two codewords. -/
def hamming_distance (c1 c2 : Codeword n α) : ℕ :=
  hammingDist c1 c2

/-- `distance C d` holds when `d` is the minimum Hamming distance of code `C`: there exist
    two distinct codewords at distance exactly `d`, and no two distinct codewords are closer. -/
def distance (C : Code n α) (d : ℕ) : Prop :=
  (∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hamming_distance x y = d) ∧
  (∀ z ∈ C, ∀ w ∈ C, z ≠ w → hamming_distance z w ≥ d)

/-- The rate of a code: `log_{|α|}(|C|) / n`. -/
noncomputable def rate (C : Code n α) : ℝ :=
  Real.log C.card / (n * Real.log (Fintype.card α))

/-- The Hamming weight of a codeword: its distance from the all-zeros word. -/
def weight (c : Codeword n α) : ℕ := hamming_distance c zero

/-- `max_size n d A` asserts that `A` is the maximum size of any code of block-length `n` and
    minimum distance `d`. -/
def max_size (n d A : ℕ) : Prop :=
  ∃ C : Code n α,
    distance C d ∧ C.card = A ∧ ∀ c : Code n α, distance c d → c.card ≤ C.card

/-- The minimum distance of a code is at most the block length. -/
lemma dist_le_length (C : Code n α) (d : ℕ) (h : distance C d) : d ≤ n := by
  rcases h with ⟨h1, _⟩
  rcases h1 with ⟨c₁, ⟨_, ⟨c₂, ⟨_, ⟨_, hdeq⟩⟩⟩⟩⟩
  have hle : hammingDist c₁ c₂ ≤ n :=
    calc
      hammingDist c₁ c₂ ≤ Fintype.card (Fin n) := by exact hammingDist_le_card_fintype
      _                 = n                    := by rel[Fintype.card_fin n]
  dsimp [hamming_distance] at hdeq
  rw [hdeq] at hle
  exact hle

/-- The Hamming ball of radius `l` centred at codeword `c`: the set of codewords within
    Hamming distance `l` of `c`. -/
@[simp]
def hamming_ball (l : ℕ) (c : Codeword n α) : Finset (Codeword n α) :=
  {c' : Codeword n α | hamming_distance c' c ≤ l}.toFinset

end Codeword

end CodingTheory
