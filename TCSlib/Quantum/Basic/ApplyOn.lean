/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/
import TCSlib.Quantum.Basic.Gates
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Applying a gate to chosen wires

A `k`-qubit operator `U` acts on an `n`-qubit register through an injection
`w : Fin k ↪ Fin n` naming the wires it touches: wire `j` of the gate is wire `w j` of the
register. In the usual notation this is `U ⊗ I` with the tensor factors reordered so that `U`
sits on the wires `w 0, …, w (k - 1)` [dW26, §2.1.2], [NC10, §4.5].

The definition is entrywise, with no reordering of tensor factors (plan FD-3): entry `(y, x)`
is `U (y ∘ w) (x ∘ w)` when `y` and `x` agree on every wire outside the range of `w`, and `0`
otherwise. `applyOn_castAdd_eq_reindex_kronecker` checks it against the Kronecker product when
the gate sits on the first `k` wires.

## Main definitions

* `Quantum.AgreeOff w y x` — registers `y` and `x` agree on every wire outside the range of `w`.
* `Quantum.applyOn w U` — the `k`-qubit operator `U` placed on wires `w` of `n` qubits.
* `Quantum.applyOnU w U` — the same, for a gate, as an element of `𝐔[Reg n]`.
* `Quantum.wire i` — the embedding `Fin 1 ↪ Fin n` naming wire `i`.

## Main results

* `Quantum.applyOn_one`, `Quantum.applyOn_mul`, `Quantum.applyOn_conjTranspose` — `applyOn w`
  preserves identities, products and adjoints.
* `Quantum.applyOn_mem_unitaryGroup` — it maps unitaries to unitaries.
* `Quantum.applyOn_refl` — on all wires in order, `applyOn` is the identity map.
* `Quantum.applyOn_commute_of_disjoint` — gates on disjoint wires commute.
* `Quantum.applyOn_castAdd_eq_reindex_kronecker` — on the first `k` wires, `applyOn` is
  `U ⊗ I`, reindexed.
* `Quantum.applyOn_mulVec_basis` — the image of a basis state.
* `Quantum.applyOn_wire_X_mulVec_basis` — sanity check: `X` on wire `i` flips wire `i`.

## References

* [dW26] R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415, version 6 (2026).
* [NC10] M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, 10th
  anniversary edition, Cambridge University Press, 2010.
-/

noncomputable section

namespace Quantum

open Matrix

variable {k k₁ k₂ n : ℕ}

/-- Registers `y` and `x` *agree off* the wires `w`: `y i = x i` for every wire `i` that is not
of the form `w j`. -/
def AgreeOff (w : Fin k ↪ Fin n) (y x : Reg n) : Prop :=
  ∀ i : Fin n, (∀ j : Fin k, w j ≠ i) → y i = x i

/-- `AgreeOff w y x` holds iff `y i = x i` at every wire `i` outside the range of `w`. -/
theorem agreeOff_iff (w : Fin k ↪ Fin n) (y x : Reg n) :
    AgreeOff w y x ↔ ∀ i : Fin n, (∀ j : Fin k, w j ≠ i) → y i = x i := Iff.rfl

instance (w : Fin k ↪ Fin n) (y x : Reg n) : Decidable (AgreeOff w y x) :=
  inferInstanceAs (Decidable (∀ i : Fin n, (∀ j : Fin k, w j ≠ i) → y i = x i))

/-- The operator `U` on `k` qubits placed on wires `w` of an `n`-qubit register, acting as the
identity on the other wires: entry `(y, x)` is `U (y ∘ w) (x ∘ w)` if `y` and `x` agree off
`w`, and `0` otherwise. [dW26, §2.1.2] (in tensor-product form; see the module docstring). -/
def applyOn (w : Fin k ↪ Fin n) (U : Matrix (Reg k) (Reg k) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  fun y x => if AgreeOff w y x then U (y ∘ w) (x ∘ w) else 0

/-- Entry `(y, x)` of `applyOn w U` is `U (y ∘ w) (x ∘ w)` if `AgreeOff w y x`, and `0`
otherwise. -/
theorem applyOn_apply (w : Fin k ↪ Fin n) (U : Matrix (Reg k) (Reg k) ℂ) (y x : Reg n) :
    applyOn w U y x = if AgreeOff w y x then U (y ∘ w) (x ∘ w) else 0 := rfl

/-! ### Algebraic properties -/

/-- Placing the identity on any wires gives the identity.

**Proof sketch.** Entry `(y, x)` is `[y ∘ w = x ∘ w]` when `y, x` agree off `w`, and `0`
otherwise; both cases together say `[y = x]`. -/
theorem applyOn_one (w : Fin k ↪ Fin n) : applyOn w (1 : Matrix (Reg k) (Reg k) ℂ) = 1 := by
  sorry

/-- Placing a product on wires `w` is the product of the placed factors:
`applyOn w (U V) = applyOn w U · applyOn w V`.

**Proof sketch.** Entry `(y, x)` of the right side is `∑_z applyOn w U y z · applyOn w V z x`.
Only the `z` agreeing with `x` (equivalently `y`) off `w` contribute, and these are in bijection
with `Reg k` through `z ↦ z ∘ w`, with inverse "write `u` on wires `w`, copy `x` elsewhere".
The sum becomes `∑_u U (y ∘ w) u · V u (x ∘ w)`, entry `(y ∘ w, x ∘ w)` of `U V`. If `y, x`
do not agree off `w`, every term vanishes. The bijection is the key lemma. -/
theorem applyOn_mul (w : Fin k ↪ Fin n) (U V : Matrix (Reg k) (Reg k) ℂ) :
    applyOn w (U * V) = applyOn w U * applyOn w V := by
  sorry

/-- Placing commutes with adjoints: `(applyOn w U)ᴴ = applyOn w Uᴴ`.

**Proof sketch.** `AgreeOff w y x` is symmetric in `y, x`, and entry `(y, x)` of `Uᴴ` is
`conj (U x y)`. -/
theorem applyOn_conjTranspose (w : Fin k ↪ Fin n) (U : Matrix (Reg k) (Reg k) ℂ) :
    (applyOn w U)ᴴ = applyOn w Uᴴ := by
  sorry

/-- Placing a unitary on any wires gives a unitary.

**Proof sketch.** `(applyOn w U)ᴴ · applyOn w U = applyOn w (Uᴴ U) = applyOn w 1 = 1`, by
`applyOn_conjTranspose`, `applyOn_mul` and `applyOn_one`. -/
theorem applyOn_mem_unitaryGroup (w : Fin k ↪ Fin n) {U : Matrix (Reg k) (Reg k) ℂ}
    (hU : U ∈ 𝐔[Reg k]) : applyOn w U ∈ 𝐔[Reg n] := by
  sorry

/-- The gate `U` placed on wires `w`, as an element of `𝐔[Reg n]`. -/
def applyOnU (w : Fin k ↪ Fin n) (U : Gate k) : 𝐔[Reg n] :=
  ⟨applyOn w U, applyOn_mem_unitaryGroup w U.2⟩

/-- The matrix of `applyOnU w U` is `applyOn w U`. -/
theorem applyOnU_coe (w : Fin k ↪ Fin n) (U : Gate k) :
    (applyOnU w U : Matrix (Reg n) (Reg n) ℂ) = applyOn w U := rfl

/-- On all `n` wires in their own order, `applyOn` does nothing: `applyOn id U = U`.

**Proof sketch.** Every wire is in the range, so `AgreeOff` holds vacuously, and
`y ∘ id = y`. -/
theorem applyOn_refl (U : Matrix (Reg n) (Reg n) ℂ) :
    applyOn (Function.Embedding.refl (Fin n)) U = U := by
  sorry

/-- Operators on disjoint sets of wires commute. [NC10, §4.5]

**Proof sketch.** Both products have entry `(y, x)` equal to
`U₁ (y ∘ w₁) (x ∘ w₁) · U₂ (y ∘ w₂) (x ∘ w₂)` when `y, x` agree off the union of the two ranges,
and `0` otherwise. Each side reduces to this through the bijection of `applyOn_mul`'s sketch,
applied to the intermediate register, which must agree with `y` on `w₁`'s range and with `x`
on `w₂`'s. -/
theorem applyOn_commute_of_disjoint (w₁ : Fin k₁ ↪ Fin n) (w₂ : Fin k₂ ↪ Fin n)
    (h : Disjoint (Set.range w₁) (Set.range w₂))
    (U₁ : Matrix (Reg k₁) (Reg k₁) ℂ) (U₂ : Matrix (Reg k₂) (Reg k₂) ℂ) :
    Commute (applyOn w₁ U₁) (applyOn w₂ U₂) := by
  sorry

/-- On the first `k` wires, `applyOn` is the Kronecker product `U ⊗ I`, reindexed along
`regAppendEquiv k m`. This ties `applyOn` to the tensor-product description of placing a gate.
[dW26, App. A.6]

**Proof sketch.** Under `regAppendEquiv`, the pair `(a, b)` is the register reading `a` on
wires `castAdd` and `b` on wires `natAdd` (`regAppendEquiv_apply_castAdd`, `_natAdd`). Entry
`((a, b), (a', b'))` of `U ⊗ I` is `U a a' · [b = b']`. On the `applyOn` side, the wires outside
the range of `castAddEmb` are exactly the `natAdd` wires, so `AgreeOff` says `b = b'`, and
`y ∘ castAdd = a`, `x ∘ castAdd = a'`. -/
theorem applyOn_castAdd_eq_reindex_kronecker (m : ℕ) (U : Matrix (Reg k) (Reg k) ℂ) :
    applyOn (Fin.castAddEmb m) U =
      reindex (regAppendEquiv k m) (regAppendEquiv k m)
        (kroneckerMap (· * ·) U (1 : Matrix (Reg m) (Reg m) ℂ)) := by
  sorry

/-! ### Action on basis states -/

/-- The image of a basis state: `applyOn w U |x⟩` has amplitude `U (y ∘ w) (x ∘ w)` at each `y`
agreeing with `x` off `w`, and `0` elsewhere.

**Proof sketch.** Column `x` of a matrix is its product with `|x⟩`
(`Matrix.mulVec_single`-style computation), and column `x` of `applyOn w U` is read off
`applyOn_apply`. -/
theorem applyOn_mulVec_basis (w : Fin k ↪ Fin n) (U : Matrix (Reg k) (Reg k) ℂ) (x : Reg n) :
    applyOn w U *ᵥ (Ket.basis x).vec =
      fun y => if AgreeOff w y x then U (y ∘ w) (x ∘ w) else 0 := by
  sorry

/-- The embedding `Fin 1 ↪ Fin n` naming the single wire `i`. -/
def wire (i : Fin n) : Fin 1 ↪ Fin n := ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩

/-- `wire i` sends the gate's only wire to `i`. -/
theorem wire_apply (i : Fin n) (j : Fin 1) : wire i j = i := rfl

/-- Sanity check for the definition of `applyOn`: the NOT gate placed on wire `i` maps the
basis state `|x⟩` to `|x with wire i flipped⟩`. [dW26, §1.4]

**Proof sketch.** By `applyOn_mulVec_basis`, the amplitude at `y` is `X (y ∘ wire i) (x ∘ wire i)`
when `y` agrees with `x` off `i`; that is `1` exactly when `y i = x i + 1`, i.e.
`y = flipAt i x`. -/
theorem applyOn_wire_X_mulVec_basis (i : Fin n) (x : Reg n) :
    applyOn (wire i) (Gate.X : Matrix (Reg 1) (Reg 1) ℂ) *ᵥ (Ket.basis x).vec =
      (Ket.basis (flipAt i x)).vec := by
  sorry

end Quantum
