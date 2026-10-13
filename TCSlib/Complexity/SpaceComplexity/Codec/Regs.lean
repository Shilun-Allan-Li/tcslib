/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The register file of the codec machine

The codec machine `Complexity.Codec.CA` works over 21 registers. This file names them
(`Complexity.Codec.rL`, …), packages register valuations as a structure with named fields
(`Complexity.Codec.Regs`, all fields `0` by default), and proves that writing a register of a
register file's valuation is the valuation of the updated structure — so that runs of the
machine can be tracked as structure updates.

Logspace machine infrastructure for the codec; not a result of [AB09].

## Main definitions

* `Complexity.Codec.Regs`, `Complexity.Codec.Regs.val` — register files and their valuations.
* `Complexity.Codec.Regs.Bd` — all registers bounded.

## Main results

* `Complexity.Codec.Regs.upd_L` and siblings — register writes on register files.
* `Complexity.Codec.Regs.Bd.val_le` — bounded register files have bounded valuations.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.Codec

/-! ## Registers -/
/-- Register `L`. -/
abbrev rL : Fin 21 := 0
/-- Register `P`. -/
abbrev rP : Fin 21 := 1
/-- Register `A`. -/
abbrev rA : Fin 21 := 2
/-- Register `B`. -/
abbrev rB : Fin 21 := 3
/-- Register `S`. -/
abbrev rS : Fin 21 := 4
/-- Register `N1`. -/
abbrev rN1 : Fin 21 := 5
/-- Register `Wp`. -/
abbrev rWp : Fin 21 := 6
/-- Register `E`. -/
abbrev rE : Fin 21 := 7
/-- Register `F`. -/
abbrev rF : Fin 21 := 8
/-- Register `E2`. -/
abbrev rE2 : Fin 21 := 9
/-- Register `F2`. -/
abbrev rF2 : Fin 21 := 10
/-- Register `Pos`. -/
abbrev rPos : Fin 21 := 11
/-- Register `Pos2`. -/
abbrev rPos2 : Fin 21 := 12
/-- Register `T`. -/
abbrev rT : Fin 21 := 13
/-- Register `U`. -/
abbrev rU : Fin 21 := 14
/-- Register `Q1`. -/
abbrev rQ1 : Fin 21 := 15
/-- Register `Q2`. -/
abbrev rQ2 : Fin 21 := 16
/-- Register `Q3`. -/
abbrev rQ3 : Fin 21 := 17
/-- Register `Q4`. -/
abbrev rQ4 : Fin 21 := 18
/-- Register `Cap`. -/
abbrev rCap : Fin 21 := 19
/-- Register `Z`. -/
abbrev rZ : Fin 21 := 20
/-- The register file of the codec deciders, by name (all `0` by default). -/
structure Regs where
  /-- register `L` -/
  L : ℕ := 0
  /-- register `P` -/
  P : ℕ := 0
  /-- register `A` -/
  A : ℕ := 0
  /-- register `B` -/
  B : ℕ := 0
  /-- register `S` -/
  S : ℕ := 0
  /-- register `N1` -/
  N1 : ℕ := 0
  /-- register `Wp` -/
  Wp : ℕ := 0
  /-- register `E` -/
  E : ℕ := 0
  /-- register `F` -/
  F : ℕ := 0
  /-- register `E2` -/
  E2 : ℕ := 0
  /-- register `F2` -/
  F2 : ℕ := 0
  /-- register `Pos` -/
  Pos : ℕ := 0
  /-- register `Pos2` -/
  Pos2 : ℕ := 0
  /-- register `T` -/
  T : ℕ := 0
  /-- register `U` -/
  U : ℕ := 0
  /-- register `Q1` -/
  Q1 : ℕ := 0
  /-- register `Q2` -/
  Q2 : ℕ := 0
  /-- register `Q3` -/
  Q3 : ℕ := 0
  /-- register `Q4` -/
  Q4 : ℕ := 0
  /-- register `Cap` -/
  Cap : ℕ := 0
  /-- register `Z` -/
  Z : ℕ := 0

/-- The register valuation of a register file. -/
def Regs.val (R : Regs) : Fin 21 → ℕ
  | ⟨0, _⟩ => R.L
  | ⟨1, _⟩ => R.P
  | ⟨2, _⟩ => R.A
  | ⟨3, _⟩ => R.B
  | ⟨4, _⟩ => R.S
  | ⟨5, _⟩ => R.N1
  | ⟨6, _⟩ => R.Wp
  | ⟨7, _⟩ => R.E
  | ⟨8, _⟩ => R.F
  | ⟨9, _⟩ => R.E2
  | ⟨10, _⟩ => R.F2
  | ⟨11, _⟩ => R.Pos
  | ⟨12, _⟩ => R.Pos2
  | ⟨13, _⟩ => R.T
  | ⟨14, _⟩ => R.U
  | ⟨15, _⟩ => R.Q1
  | ⟨16, _⟩ => R.Q2
  | ⟨17, _⟩ => R.Q3
  | ⟨18, _⟩ => R.Q4
  | ⟨19, _⟩ => R.Cap
  | _ => R.Z

/-- Reading register `L`. -/
@[simp] lemma Regs.val_L (R : Regs) : R.val rL = R.L := rfl

/-- Reading register `P`. -/
@[simp] lemma Regs.val_P (R : Regs) : R.val rP = R.P := rfl

/-- Reading register `A`. -/
@[simp] lemma Regs.val_A (R : Regs) : R.val rA = R.A := rfl

/-- Reading register `B`. -/
@[simp] lemma Regs.val_B (R : Regs) : R.val rB = R.B := rfl

/-- Reading register `S`. -/
@[simp] lemma Regs.val_S (R : Regs) : R.val rS = R.S := rfl

/-- Reading register `N1`. -/
@[simp] lemma Regs.val_N1 (R : Regs) : R.val rN1 = R.N1 := rfl

/-- Reading register `Wp`. -/
@[simp] lemma Regs.val_Wp (R : Regs) : R.val rWp = R.Wp := rfl

/-- Reading register `E`. -/
@[simp] lemma Regs.val_E (R : Regs) : R.val rE = R.E := rfl

/-- Reading register `F`. -/
@[simp] lemma Regs.val_F (R : Regs) : R.val rF = R.F := rfl

/-- Reading register `E2`. -/
@[simp] lemma Regs.val_E2 (R : Regs) : R.val rE2 = R.E2 := rfl

/-- Reading register `F2`. -/
@[simp] lemma Regs.val_F2 (R : Regs) : R.val rF2 = R.F2 := rfl

/-- Reading register `Pos`. -/
@[simp] lemma Regs.val_Pos (R : Regs) : R.val rPos = R.Pos := rfl

/-- Reading register `Pos2`. -/
@[simp] lemma Regs.val_Pos2 (R : Regs) : R.val rPos2 = R.Pos2 := rfl

/-- Reading register `T`. -/
@[simp] lemma Regs.val_T (R : Regs) : R.val rT = R.T := rfl

/-- Reading register `U`. -/
@[simp] lemma Regs.val_U (R : Regs) : R.val rU = R.U := rfl

/-- Reading register `Q1`. -/
@[simp] lemma Regs.val_Q1 (R : Regs) : R.val rQ1 = R.Q1 := rfl

/-- Reading register `Q2`. -/
@[simp] lemma Regs.val_Q2 (R : Regs) : R.val rQ2 = R.Q2 := rfl

/-- Reading register `Q3`. -/
@[simp] lemma Regs.val_Q3 (R : Regs) : R.val rQ3 = R.Q3 := rfl

/-- Reading register `Q4`. -/
@[simp] lemma Regs.val_Q4 (R : Regs) : R.val rQ4 = R.Q4 := rfl

/-- Reading register `Cap`. -/
@[simp] lemma Regs.val_Cap (R : Regs) : R.val rCap = R.Cap := rfl

/-- Reading register `Z`. -/
@[simp] lemma Regs.val_Z (R : Regs) : R.val rZ = R.Z := rfl

/-- Writing register `L`. -/
@[simp] lemma Regs.upd_L (R : Regs) (v : ℕ) :
    Function.update R.val rL v = ({ R with L := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `P`. -/
@[simp] lemma Regs.upd_P (R : Regs) (v : ℕ) :
    Function.update R.val rP v = ({ R with P := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `A`. -/
@[simp] lemma Regs.upd_A (R : Regs) (v : ℕ) :
    Function.update R.val rA v = ({ R with A := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `B`. -/
@[simp] lemma Regs.upd_B (R : Regs) (v : ℕ) :
    Function.update R.val rB v = ({ R with B := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `S`. -/
@[simp] lemma Regs.upd_S (R : Regs) (v : ℕ) :
    Function.update R.val rS v = ({ R with S := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `N1`. -/
@[simp] lemma Regs.upd_N1 (R : Regs) (v : ℕ) :
    Function.update R.val rN1 v = ({ R with N1 := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `Wp`. -/
@[simp] lemma Regs.upd_Wp (R : Regs) (v : ℕ) :
    Function.update R.val rWp v = ({ R with Wp := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `E`. -/
@[simp] lemma Regs.upd_E (R : Regs) (v : ℕ) :
    Function.update R.val rE v = ({ R with E := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `F`. -/
@[simp] lemma Regs.upd_F (R : Regs) (v : ℕ) :
    Function.update R.val rF v = ({ R with F := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `E2`. -/
@[simp] lemma Regs.upd_E2 (R : Regs) (v : ℕ) :
    Function.update R.val rE2 v = ({ R with E2 := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `F2`. -/
@[simp] lemma Regs.upd_F2 (R : Regs) (v : ℕ) :
    Function.update R.val rF2 v = ({ R with F2 := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `Pos`. -/
@[simp] lemma Regs.upd_Pos (R : Regs) (v : ℕ) :
    Function.update R.val rPos v = ({ R with Pos := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `Pos2`. -/
@[simp] lemma Regs.upd_Pos2 (R : Regs) (v : ℕ) :
    Function.update R.val rPos2 v = ({ R with Pos2 := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `T`. -/
@[simp] lemma Regs.upd_T (R : Regs) (v : ℕ) :
    Function.update R.val rT v = ({ R with T := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `U`. -/
@[simp] lemma Regs.upd_U (R : Regs) (v : ℕ) :
    Function.update R.val rU v = ({ R with U := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `Q1`. -/
@[simp] lemma Regs.upd_Q1 (R : Regs) (v : ℕ) :
    Function.update R.val rQ1 v = ({ R with Q1 := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `Q2`. -/
@[simp] lemma Regs.upd_Q2 (R : Regs) (v : ℕ) :
    Function.update R.val rQ2 v = ({ R with Q2 := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `Q3`. -/
@[simp] lemma Regs.upd_Q3 (R : Regs) (v : ℕ) :
    Function.update R.val rQ3 v = ({ R with Q3 := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `Q4`. -/
@[simp] lemma Regs.upd_Q4 (R : Regs) (v : ℕ) :
    Function.update R.val rQ4 v = ({ R with Q4 := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `Cap`. -/
@[simp] lemma Regs.upd_Cap (R : Regs) (v : ℕ) :
    Function.update R.val rCap v = ({ R with Cap := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- Writing register `Z`. -/
@[simp] lemma Regs.upd_Z (R : Regs) (v : ℕ) :
    Function.update R.val rZ v = ({ R with Z := v } : Regs).val := by
  funext r; fin_cases r <;> rfl

/-- All registers of a register file are at most `B`. -/
def Regs.Bd (R : Regs) (B : ℕ) : Prop :=
  R.L ≤ B ∧ R.P ≤ B ∧ R.A ≤ B ∧ R.B ≤ B ∧ R.S ≤ B ∧ R.N1 ≤ B ∧ R.Wp ≤ B ∧ R.E ≤ B ∧ R.F ≤ B ∧ R.E2 ≤ B ∧ R.F2 ≤ B ∧ R.Pos ≤ B ∧ R.Pos2 ≤ B ∧ R.T ≤ B ∧ R.U ≤ B ∧ R.Q1 ≤ B ∧ R.Q2 ≤ B ∧ R.Q3 ≤ B ∧ R.Q4 ≤ B ∧ R.Cap ≤ B ∧ R.Z ≤ B

/-- A bounded register file has a bounded valuation. -/
lemma Regs.Bd.val_le {R : Regs} {B : ℕ} (h : R.Bd B) : ∀ r, R.val r ≤ B := by
  obtain ⟨hL, hP, hA, hB, hS, hN1, hWp, hE, hF, hE2, hF2, hPos, hPos2, hT, hU, hQ1, hQ2, hQ3, hQ4, hCap, hZ⟩ := h
  intro r; fin_cases r <;> assumption

end Complexity.Codec
