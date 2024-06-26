/-
Copyright (c) 2024 Shilun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shilun Li
-/

import Mathlib.Logic.Equiv.Fin
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Basic
import Mathlib.Init.Set

/-!
# Code Definitions

`Code n 𝔽`: a subset of 𝔽ⁿ.
`AsymptoticCodes 𝔽`: a map from ℕ to `Code n 𝔽`.

-/

open Set Filter Asymptotics Finset

namespace CodingTheory

-- variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
variable {α : Type*} [Fintype α] [DecidableEq α] -- the alphabet
variable {n k : ℕ}


/-- An element of 𝔽ⁿ. -/
abbrev Codeword (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] := (i : Fin n) → α


/-- Code `Code n 𝔽` is a subset of 𝔽ⁿ. -/
abbrev Code (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] := Finset (Codeword n α)


/-- AsymptoticCodes is a map from ℕ to `Code n 𝔽`. -/
-- def AsymptoticCodes (α : Type*) (S : Set ℕ) (hs : S.Infinite) [Fintype α] [DecidableEq α] :=  (n : S) → Code n α


def hamming_distance (c1 c2 : Codeword n α) : ℕ :=
  hammingDist c1 c2


def distance (C : Code n α) (d : ℕ) : Prop :=
  (∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hamming_distance x y = d) ∧ (∀ z ∈ C, ∀ w ∈ C, z ≠ w → hamming_distance z w ≥ d)


theorem singleton_bound (C : Code n α) (d : ℕ) : C.card ≤ (Fintype.card α)^(n - d + 1) :=
  sorry


theorem hamming_bound (C : Code n α) (d : ℕ) : C.card ≤ (Fintype.card α)^n / Finset.sum (Finset.range (d + 1)) (λ i=> Nat.choose n i * (q - 1)^i) :=
  sorry
