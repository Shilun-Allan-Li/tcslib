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

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
variable {α : Type} [Fintype 𝔽] [DecidableEq α]
variable {n k : ℕ}


/-- A type that represents the set of symbols in the code -/
def Alphabet := Set α


/-- An element of 𝔽ⁿ. -/
def Codeword (n : ℕ) (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] := Fin n → 𝔽


/-- Code `Code n 𝔽` is a subset of 𝔽ⁿ. -/
def Code (n : ℕ) (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] := Finset (Codeword n 𝔽)


/-- AsymptoticCodes is a map from ℕ to `Code n 𝔽`. -/
def AsymptoticCodes (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :=  (n : ℕ) → Code n 𝔽


def hamming_distance (c1 c2 : Codeword n 𝔽) : ℕ :=
  hammingDist c1 c2


-- def distance {n : ℕ} (C : Code n 𝔽) : ℕ :=
--   min {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hamming_distance x y = d}
