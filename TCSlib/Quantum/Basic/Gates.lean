/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/
import TCSlib.Quantum.Basic.Register
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Elementary gates

The gates of [Wat08, §III.2] and [dW26, §1.4], as unitaries on small registers. A `k`-qubit
gate is an element of `Gate k = 𝐔[Reg k]`; `Quantum.applyOn` (in `ApplyOn.lean`) places it on
chosen wires of a larger register.

Two constructions cover most gates. A *classical* gate permutes the basis states
(`Gate.ofPerm`): `X`, `CNOT` and `Toffoli` are of this kind. A *phase* gate multiplies each
basis state by a unit complex number (`Gate.ofPhase`): `Z` and `S` are of this kind. The
Hadamard gate `H` is neither.

## Main definitions

* `Quantum.permMat` — the permutation matrix of a bijection of the basis.
* `Quantum.Gate k` — the `k`-qubit gates, `𝐔[Reg k]`.
* `Quantum.Gate.ofPerm`, `Quantum.Gate.ofPhase` — classical and phase gates.
* `Quantum.flipAt`, `Quantum.cnotMap`, `Quantum.toffoliMap` — the bit maps of `X`, `CNOT`,
  `Toffoli`.
* `Quantum.Gate.H`, `Gate.X`, `Gate.Z`, `Gate.S`, `Gate.CNOT`, `Gate.Toffoli` — the named gates.
  `Gate.S` is the phase-shift gate `P : |a⟩ ↦ iᵃ|a⟩` of [Wat08, §III.2].

## Main results

* `Quantum.permMat_mem_unitaryGroup`, `Quantum.diagonal_mem_unitaryGroup` — classical and
  phase gates are unitary.
* `Quantum.permMat_mulVec_basis` — a classical gate maps `|x⟩` to `|σ x⟩`.
* `Quantum.Gate.H_mul_H`, `Quantum.Gate.S_mul_S`, `Quantum.Gate.H_mul_Z_mul_H` — gate
  identities.
* `Quantum.Gate.X_eq_H_mul_S_mul_S_mul_H` — the NOT gate from Hadamard and phase gates
  [Wat08, Fig. 4].
* `Quantum.Gate.Toffoli_apply_of_control_one` — a Toffoli gate whose first control is `|1⟩` acts
  as `CNOT` on the other two wires [Wat08, Fig. 4].

## Divergences

* [Physlib] defines its single-qubit gates on `Qubit` and `CNOT` on `Qubit × Qubit`. Here every
  `k`-qubit gate lives on `Reg k = Fin k → Qubit`, the shape `applyOn` needs. The names are
  [Physlib]'s; the bridge is a relabelling along `Reg 1 ≃ Qubit` and `Reg 2 ≃ Qubit × Qubit`,
  to be stated when the [Physlib] dependency arrives (plan OQ-1).
* Wire conventions: `CNOT` has control wire `0` and target wire `1`; `Toffoli` has controls
  `0, 1` and target `2`.

## References

* [Wat08] J. Watrous, *Quantum Computational Complexity*, arXiv:0804.3401, 2008.
* [dW26] R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415, version 6 (2026).
* [Physlib] leanprover-community/physlib, `QuantumInfo/States/Pure/Qubit.lean`, commit
  cdfa6094901b8956a378151f64088bcf5a5f8bcb, Apache-2.0. Design adapted, no code transcribed:
  the gate names `H`, `X`, `Z`, `S`, `CNOT`.
-/

noncomputable section

namespace Quantum

open Matrix

/-! ### Classical and phase gates -/

section Constructions

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The permutation matrix of a bijection `σ` of the basis: entry `(y, x)` is `1` if
`y = σ x` and `0` otherwise, so it maps `|x⟩` to `|σ x⟩`. [dW26, §1.4] -/
def permMat (σ : Equiv.Perm d) : Matrix d d ℂ := fun y x => if y = σ x then 1 else 0

omit [Fintype d] in
/-- Entry `(y, x)` of `permMat σ` is `1` if `y = σ x` and `0` otherwise. -/
theorem permMat_apply (σ : Equiv.Perm d) (y x : d) :
    permMat σ y x = if y = σ x then 1 else 0 := rfl

/-- A permutation matrix is unitary.

**Proof sketch.** `(permMat σ)ᴴ = permMat σ⁻¹`, and `permMat σ * permMat τ = permMat (σ * τ)`,
so `(permMat σ)ᴴ * permMat σ = permMat 1 = 1`. -/
theorem permMat_mem_unitaryGroup (σ : Equiv.Perm d) : permMat σ ∈ 𝐔[d] := by
  sorry

/-- A classical gate maps the basis state `|x⟩` to `|σ x⟩`. [dW26, §1.4]

**Proof sketch.** Entry `y` of `permMat σ *ᵥ |x⟩` is `permMat σ y x = [y = σ x]`. -/
theorem permMat_mulVec_basis (σ : Equiv.Perm d) (x : d) :
    permMat σ *ᵥ (Ket.basis x).vec = (Ket.basis (σ x)).vec := by
  sorry

/-- A diagonal matrix whose entries all have norm `1` is unitary. [dW26, App. A.4]

**Proof sketch.** `(diagonal f)ᴴ * diagonal f = diagonal (fun x => conj (f x) * f x)`, and
`conj z * z = ‖z‖² = 1`. -/
theorem diagonal_mem_unitaryGroup (f : d → ℂ) (hf : ∀ x, ‖f x‖ = 1) :
    diagonal f ∈ 𝐔[d] := by
  sorry

end Constructions

/-- The `k`-qubit gates: unitaries on the basis `Reg k`. -/
abbrev Gate (k : ℕ) := 𝐔[Reg k]

namespace Gate

variable {k : ℕ}

/-- The classical gate that permutes the basis states of `Reg k` by `σ`. -/
def ofPerm (σ : Equiv.Perm (Reg k)) : Gate k := ⟨permMat σ, permMat_mem_unitaryGroup σ⟩

/-- The matrix of `ofPerm σ` is `permMat σ`. -/
theorem ofPerm_coe (σ : Equiv.Perm (Reg k)) : (ofPerm σ : Matrix (Reg k) (Reg k) ℂ) = permMat σ :=
  rfl

/-- The phase gate that multiplies each basis state `|x⟩` by the unit complex number `f x`. -/
def ofPhase (f : Reg k → ℂ) (hf : ∀ x, ‖f x‖ = 1) : Gate k :=
  ⟨diagonal f, diagonal_mem_unitaryGroup f hf⟩

/-- The matrix of `ofPhase f hf` is `diagonal f`. -/
theorem ofPhase_coe (f : Reg k → ℂ) (hf : ∀ x, ‖f x‖ = 1) :
    (ofPhase f hf : Matrix (Reg k) (Reg k) ℂ) = diagonal f := rfl

end Gate

/-! ### Bit maps -/

/-- Flip wire `i`: the register equal to `x` except that wire `i` holds `x i + 1` (NOT). -/
def flipAt {n : ℕ} (i : Fin n) (x : Reg n) : Reg n := Function.update x i (x i + 1)

/-- `flipAt i x` is `x` with wire `i` replaced by `x i + 1`. -/
theorem flipAt_eq {n : ℕ} (i : Fin n) (x : Reg n) :
    flipAt i x = Function.update x i (x i + 1) := rfl

/-- Flipping the same wire twice restores the register.

**Proof sketch.** Pointwise: at wire `i` the value is `x i + 1 + 1 = x i` in `Fin 2`; elsewhere
`Function.update` leaves `x` unchanged. -/
theorem flipAt_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flipAt i) := by
  sorry

/-- The bit map of `CNOT`: `(a, b) ↦ (a, b ⊕ a)`, control wire `0`, target wire `1`. -/
def cnotMap (x : Reg 2) : Reg 2 := Function.update x 1 (x 1 + x 0)

/-- `cnotMap x` is `x` with wire `1` replaced by `x 1 + x 0`. -/
theorem cnotMap_eq (x : Reg 2) : cnotMap x = Function.update x 1 (x 1 + x 0) := rfl

/-- `cnotMap` is an involution (checked on all four basis states). -/
theorem cnotMap_involutive : Function.Involutive cnotMap := by
  intro x
  revert x
  decide

/-- The bit map of `Toffoli`: `(a, b, c) ↦ (a, b, c ⊕ ab)`, controls `0, 1`, target `2`.
[Wat08, §III.2] -/
def toffoliMap (x : Reg 3) : Reg 3 := Function.update x 2 (x 2 + x 0 * x 1)

/-- `toffoliMap x` is `x` with wire `2` replaced by `x 2 + x 0 * x 1`. -/
theorem toffoliMap_eq (x : Reg 3) : toffoliMap x = Function.update x 2 (x 2 + x 0 * x 1) := rfl

/-- `toffoliMap` is an involution (checked on all eight basis states). -/
theorem toffoliMap_involutive : Function.Involutive toffoliMap := by
  intro x
  revert x
  decide

/-! ### The Hadamard matrix and the phases of `Z` and `S` -/

/-- The Hadamard matrix on one qubit: entry `(y, x)` is `(-1)^(x·y) / √2`. [Wat08, §III.2],
[dW26, §1.4] -/
def hadamardMat : Matrix (Reg 1) (Reg 1) ℂ :=
  fun y x => ((Real.sqrt 2)⁻¹ : ℂ) * (-1) ^ ((x 0 * y 0 : Qubit) : ℕ)

/-- Entry `(y, x)` of `hadamardMat` is `(-1)^(x·y) / √2`. -/
theorem hadamardMat_apply (y x : Reg 1) :
    hadamardMat y x = ((Real.sqrt 2)⁻¹ : ℂ) * (-1) ^ ((x 0 * y 0 : Qubit) : ℕ) := rfl

/-- The Hadamard matrix is unitary.

**Proof sketch.** It is real and symmetric, so its adjoint is itself; its square is the identity
by direct computation of the four entries (`(1 + 1)/2 = 1`, `(1 - 1)/2 = 0`). -/
theorem hadamardMat_mem_unitaryGroup : hadamardMat ∈ 𝐔[Reg 1] := by
  sorry

/-- The phase of `Z`: `(-1)^a` on `|a⟩`. -/
def zPhase (x : Reg 1) : ℂ := (-1) ^ ((x 0 : Qubit) : ℕ)

/-- `zPhase x = (-1)^(x 0)`. -/
theorem zPhase_eq (x : Reg 1) : zPhase x = (-1) ^ ((x 0 : Qubit) : ℕ) := rfl

/-- The phases of `Z` have norm `1`.

**Proof sketch.** `‖(-1)ⁿ‖ = ‖-1‖ⁿ = 1` (`norm_pow`, `norm_neg`, `norm_one`). -/
theorem norm_zPhase (x : Reg 1) : ‖zPhase x‖ = 1 := by
  sorry

/-- The phase of `S` (Watrous's `P`): `iᵃ` on `|a⟩`. [Wat08, §III.2] -/
def sPhase (x : Reg 1) : ℂ := Complex.I ^ ((x 0 : Qubit) : ℕ)

/-- `sPhase x = i^(x 0)`. -/
theorem sPhase_eq (x : Reg 1) : sPhase x = Complex.I ^ ((x 0 : Qubit) : ℕ) := rfl

/-- The phases of `S` have norm `1`.

**Proof sketch.** `‖iⁿ‖ = ‖i‖ⁿ = 1` (`norm_pow`, `Complex.norm_I`). -/
theorem norm_sPhase (x : Reg 1) : ‖sPhase x‖ = 1 := by
  sorry

/-! ### The named gates -/

namespace Gate

/-- The Hadamard gate `H : |a⟩ ↦ (|0⟩ + (-1)ᵃ|1⟩)/√2`. [Wat08, §III.2], [dW26, §1.4] -/
def H : Gate 1 := ⟨hadamardMat, hadamardMat_mem_unitaryGroup⟩

/-- The matrix of `H` is `hadamardMat`. -/
theorem H_coe : (H : Matrix (Reg 1) (Reg 1) ℂ) = hadamardMat := rfl

/-- The NOT gate `X : |a⟩ ↦ |1 - a⟩`. [dW26, §1.4] -/
def X : Gate 1 := ofPerm (Function.Involutive.toPerm (flipAt 0) (flipAt_involutive 0))

/-- The matrix of `X` is the permutation matrix of `flipAt 0`. -/
theorem X_coe :
    (X : Matrix (Reg 1) (Reg 1) ℂ) =
      permMat (Function.Involutive.toPerm (flipAt 0) (flipAt_involutive 0)) := rfl

/-- The phase-flip gate `Z : |a⟩ ↦ (-1)ᵃ|a⟩`. [dW26, §1.4] -/
def Z : Gate 1 := ofPhase zPhase norm_zPhase

/-- The matrix of `Z` is `diagonal zPhase`. -/
theorem Z_coe : (Z : Matrix (Reg 1) (Reg 1) ℂ) = diagonal zPhase := rfl

/-- The phase-shift gate `S : |a⟩ ↦ iᵃ|a⟩`, the gate `P` of [Wat08, §III.2]. -/
def S : Gate 1 := ofPhase sPhase norm_sPhase

/-- The matrix of `S` is `diagonal sPhase`. -/
theorem S_coe : (S : Matrix (Reg 1) (Reg 1) ℂ) = diagonal sPhase := rfl

/-- The controlled-NOT gate `|a, b⟩ ↦ |a, b ⊕ a⟩` (control wire `0`). [dW26, §1.4] -/
def CNOT : Gate 2 := ofPerm (Function.Involutive.toPerm cnotMap cnotMap_involutive)

/-- The matrix of `CNOT` is the permutation matrix of `cnotMap`. -/
theorem CNOT_coe :
    (CNOT : Matrix (Reg 2) (Reg 2) ℂ) =
      permMat (Function.Involutive.toPerm cnotMap cnotMap_involutive) := rfl

/-- The Toffoli gate `|a, b, c⟩ ↦ |a, b, c ⊕ ab⟩` (controls `0, 1`). [Wat08, §III.2] -/
def Toffoli : Gate 3 := ofPerm (Function.Involutive.toPerm toffoliMap toffoliMap_involutive)

/-- The matrix of `Toffoli` is the permutation matrix of `toffoliMap`. -/
theorem Toffoli_coe :
    (Toffoli : Matrix (Reg 3) (Reg 3) ℂ) =
      permMat (Function.Involutive.toPerm toffoliMap toffoliMap_involutive) := rfl

/-! ### Gate identities -/

/-- The Hadamard gate is its own inverse: `H H = 1`. [dW26, §1.4]

**Proof sketch.** Entry `(y, x)` of `H H` is `(1/2) ∑_z (-1)^{z(x + y)}`, which is `1` if
`x = y` and `0` otherwise. -/
theorem H_mul_H : H * H = 1 := by
  sorry

/-- The NOT gate is its own inverse: `X X = 1` (round-1 audit, sanity statement 3).

**Proof sketch.** `X` is the permutation gate of the involution `flipAt 0`, and
`permMat σ * permMat σ = permMat (σ * σ) = permMat 1 = 1`. -/
theorem X_mul_X : X * X = 1 := by
  sorry

/-- The phase flip is its own inverse: `Z Z = 1` (round-1 audit, sanity statement 3).

**Proof sketch.** Diagonal matrices multiply entrywise, and `((-1)^a)² = 1`. -/
theorem Z_mul_Z : Z * Z = 1 := by
  sorry

/-- The NOT gate is not the identity, so the gate definitions are not degenerate (round-1 audit,
sanity statement 3).

**Proof sketch.** Entry `(|1⟩, |0⟩)` of `X` is `1` (`permMat_apply`, since `flipAt 0` sends the
register `0` to `1`), while that entry of the identity is `0`. -/
theorem X_ne_one : X ≠ 1 := by
  sorry

/-- Two phase shifts make a phase flip: `S S = Z`.

**Proof sketch.** Both are diagonal; `diagonal f * diagonal g = diagonal (f * g)`, and
`iᵃ · iᵃ = (-1)ᵃ` for `a ∈ {0, 1}`. Compare as elements of the unitary group by `Subtype.ext`. -/
theorem S_mul_S : S * S = Z := by
  sorry

/-- Conjugating a phase flip by Hadamards gives a bit flip: `H Z H = X`. [dW26, §1.4]

**Proof sketch.** Entry `(y, x)` of `H Z H` is `(1/2) ∑_z (-1)^{z(x + y + 1)}`, which is `1`
if `y = x + 1` and `0` otherwise: the entries of `X`. -/
theorem H_mul_Z_mul_H : H * Z * H = X := by
  sorry

/-- The NOT gate is built from Hadamard and phase gates: `X = H P P H`. [Wat08, Fig. 4]

**Proof sketch.** `S S = Z` (`S_mul_S`) and `H Z H = X` (`H_mul_Z_mul_H`), with
associativity. -/
theorem X_eq_H_mul_S_mul_S_mul_H : X = H * S * S * H := by
  sorry

/-- A Toffoli gate whose first control is `|1⟩` acts as `CNOT` on wires `1, 2`: for basis
states `y, x` with `y 0 = x 0 = 1`, entry `(y, x)` of `Toffoli` is entry `(y ∘ succ, x ∘ succ)`
of `CNOT`. This is the controlled-NOT construction of [Wat08, Fig. 4], with the constant `|1⟩`
supplied on wire `0`.

**Proof sketch.** With `x 0 = 1`, `toffoliMap x` changes wire `2` to `x 2 + x 1`, which is
`cnotMap` on wires `1, 2`. Both entries are `1` exactly when `y` is the image of `x`, and `y 0`
matches since neither map touches wire `0`. -/
theorem Toffoli_apply_of_control_one (y x : Reg 3) (hy : y 0 = 1) (hx : x 0 = 1) :
    (Toffoli : Matrix (Reg 3) (Reg 3) ℂ) y x =
      (CNOT : Matrix (Reg 2) (Reg 2) ℂ) (fun i => y i.succ) (fun i => x i.succ) := by
  sorry

end Gate

end Quantum
