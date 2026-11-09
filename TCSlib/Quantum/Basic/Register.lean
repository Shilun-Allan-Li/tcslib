/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Qubits, registers and pure states

The state space of quantum computation [dW26, §1.2–1.3]. A qubit's computational basis is
`Fin 2`. An `n`-qubit register's basis is `Fin n → Qubit`. A pure state on a finite basis `d`
is a unit vector `d → ℂ`.

## Main definitions

* `Quantum.Qubit` — the computational basis of one qubit, `Fin 2`.
* `Quantum.Reg n` — the computational basis of `n` qubits, `Fin n → Qubit`.
* `Quantum.qubitEquivBool`, `Quantum.basisOf` — the bridge to the `Bool`-valued strings of the
  classical side of TCSlib.
* `Quantum.regAppendEquiv` — `Reg k × Reg m ≃ Reg (k + m)`, splitting a register in two.
* `Quantum.Ket d` — a unit vector over the basis `d` [dW26, §1.2.1].
* `Quantum.Ket.basis`, `Quantum.Ket.relabel`, `Quantum.Ket.prod` (`⊗ᵠ`), `Quantum.Ket.evolve` —
  basis states, relabelling, tensor products and unitary evolution [dW26, §1.2.3, App. A.6].

## Main results

* `Quantum.inner_mulVec_of_mem_unitaryGroup`, `Quantum.sum_norm_sq_mulVec_of_mem_unitaryGroup` —
  unitaries preserve inner products and squared norms.
* `Quantum.regAppendEquiv_symm_apply` — splitting a register into its first and last wires.
* The normalization lemmas behind `Ket.basis`, `Ket.relabel` and `Ket.prod`.
* `Quantum.Ket.evolve_mul`, `Quantum.Ket.evolve_one` — evolution is an action.

## Notation

* `𝐔[d]` (scoped in `Quantum`) — `Matrix.unitaryGroup d ℂ`, as in [Physlib].
* `ψ ⊗ᵠ φ` (scoped in `Quantum`) — `Ket.prod ψ φ`, as in [Physlib].

## Divergences

* Kets are read through the field `Ket.vec`; [Physlib] also makes `Ket d` a `FunLike`. The
  coercion is not added here, so that the definitions can be replaced by [Physlib]'s without
  changing how consumers read them (plan FD-2).

## References

* [dW26] R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415, version 6 (2026).
* [NC10] M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, 10th
  anniversary edition, Cambridge University Press, 2010.
* [Physlib] leanprover-community/physlib, `QuantumInfo/States/Pure/Braket.lean` and
  `QuantumInfo/States/Pure/Qubit.lean` (authors A. Meiburg, R. Soldati and contributors),
  commit cdfa6094901b8956a378151f64088bcf5a5f8bcb, Apache-2.0. Design adapted, no code
  transcribed: the `Ket` structure and its field names, `Qubit := Fin 2`, the `𝐔[d]` and `⊗ᵠ`
  notations, the names `Ket.basis`, `Ket.relabel`, `Ket.prod`.
-/

namespace Quantum

open Matrix

/-- The computational basis of one qubit: `0` and `1`, as `Fin 2`. Addition in `Fin 2` is XOR
and multiplication is AND. [dW26, §1.3]; the type follows [Physlib]. -/
abbrev Qubit := Fin 2

/-- The computational basis of an `n`-qubit register: one `Qubit` per wire. [dW26, §1.3] -/
abbrev Reg (n : ℕ) := Fin n → Qubit

/-- `𝐔[d]` is the group of `d × d` complex unitary matrices. Notation as in [Physlib]. -/
scoped notation "𝐔[" d "]" => Matrix.unitaryGroup d ℂ

/-! ### The bridge to `Bool` -/

/-- The identification of a qubit's basis with `Bool`: `0 ↦ false`, `1 ↦ true`. It is
Mathlib's `finTwoEquiv`. -/
def qubitEquivBool : Qubit ≃ Bool := finTwoEquiv

/-- `qubitEquivBool` is `finTwoEquiv`. -/
theorem qubitEquivBool_eq : qubitEquivBool = finTwoEquiv := rfl

/-- `qubitEquivBool` sends the qubit `0` to `false` (round-1 audit, sanity statement 1). -/
theorem qubitEquivBool_zero : qubitEquivBool 0 = false := by
  decide

/-- `qubitEquivBool` sends the qubit `1` to `true` (round-1 audit, sanity statement 1). -/
theorem qubitEquivBool_one : qubitEquivBool 1 = true := by
  decide

/-- An `n`-qubit register has `2ⁿ` basis states; in particular `Reg 0` has exactly one, so the
zero-qubit state space is one-dimensional, not empty (round-1 audit, sanity statement 1).

**Proof sketch.** `Fintype.card_fun`, `Fintype.card_fin`. -/
theorem card_reg (n : ℕ) : Fintype.card (Reg n) = 2 ^ n := by
  simp

/-- The register basis state spelling out a `Bool` string: wire `i` holds the qubit
corresponding to `x i`. -/
def basisOf {n : ℕ} (x : Fin n → Bool) : Reg n := fun i => qubitEquivBool.symm (x i)

/-- Wire `i` of `basisOf x` is `qubitEquivBool.symm (x i)`. -/
theorem basisOf_apply {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    basisOf x i = qubitEquivBool.symm (x i) := rfl

/-! ### Splitting a register -/

/-- A register of `k + m` wires is a pair of registers: the first `k` wires and the last `m`.
The pair `(a, b)` corresponds to the register reading `a` on wires `0, …, k - 1` and `b` on
wires `k, …, k + m - 1`. -/
def regAppendEquiv (k m : ℕ) : Reg k × Reg m ≃ Reg (k + m) :=
  (Equiv.sumArrowEquivProdArrow (Fin k) (Fin m) Qubit).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl Qubit))

/-- On the first `k` wires, `regAppendEquiv k m (a, b)` reads `a`.

**Proof sketch.** Unfold the two equivalences: `finSumFinEquiv.symm (castAdd m i) = inl i`
(`finSumFinEquiv_symm_apply_castAdd`), and `Sum.elim a b (inl i) = a i`. -/
theorem regAppendEquiv_apply_castAdd (k m : ℕ) (a : Reg k) (b : Reg m) (i : Fin k) :
    regAppendEquiv k m (a, b) (Fin.castAdd m i) = a i := by
  simp [regAppendEquiv]

/-- On the last `m` wires, `regAppendEquiv k m (a, b)` reads `b`.

**Proof sketch.** As for `regAppendEquiv_apply_castAdd`, with
`finSumFinEquiv.symm (natAdd k i) = inr i`. -/
theorem regAppendEquiv_apply_natAdd (k m : ℕ) (a : Reg k) (b : Reg m) (i : Fin m) :
    regAppendEquiv k m (a, b) (Fin.natAdd k i) = b i := by
  simp [regAppendEquiv]

/-- Splitting a register of `k + m` wires gives its first `k` wires and its last `m` wires:
`(regAppendEquiv k m).symm y = (y ∘ castAdd m, y ∘ natAdd k)`. Promoted from a private lemma of
`ApplyOn.lean` during fill epoch E1, so that `Protocols.lean` can use it without a copy.

**Proof sketch.** Apply `regAppendEquiv k m` to both sides and compare wire by wire
(`Fin.addCases`), using `regAppendEquiv_apply_castAdd` and `regAppendEquiv_apply_natAdd`. -/
theorem regAppendEquiv_symm_apply (k m : ℕ) (y : Reg (k + m)) :
    (regAppendEquiv k m).symm y = (fun i => y (Fin.castAdd m i), fun i => y (Fin.natAdd k i)) := by
  apply (regAppendEquiv k m).injective
  rw [Equiv.apply_symm_apply]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [regAppendEquiv_apply_castAdd]
  · rw [regAppendEquiv_apply_natAdd]

/-! ### Norm identities behind the constructions -/

section Norms

variable {d d₁ d₂ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂]

/-- A standard basis vector has squared norm `1`: `∑ⱼ ‖[i = j]‖² = 1`.

**Proof sketch.** Only the term `j = i` is nonzero (`Finset.sum_ite_eq`), and it is
`‖1‖² = 1`. -/
theorem sum_norm_sq_basisVec [DecidableEq d] (i : d) :
    ∑ j, ‖(if i = j then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
  simp [apply_ite]

/-- Relabelling the basis along an equivalence does not change the squared norm.

**Proof sketch.** Reindex the sum along `e` (`Equiv.sum_comp`). -/
theorem sum_norm_sq_comp_equiv (v : d₁ → ℂ) (e : d₂ ≃ d₁) :
    ∑ i, ‖v (e i)‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 :=
  Equiv.sum_comp e (fun j => ‖v j‖ ^ 2)

/-- The squared norm is multiplicative on tensor products:
`∑_{(i,j)} ‖v i · w j‖² = (∑ᵢ ‖v i‖²)(∑ⱼ ‖w j‖²)`. [dW26, App. A.6]

**Proof sketch.** Split the sum over the product type, use `‖ab‖² = ‖a‖²‖b‖²`, and factor. -/
theorem sum_norm_sq_mul_prod (v : d₁ → ℂ) (w : d₂ → ℂ) :
    ∑ p : d₁ × d₂, ‖v p.1 * w p.2‖ ^ 2 = (∑ i, ‖v i‖ ^ 2) * (∑ j, ‖w j‖ ^ 2) := by
  simp only [Fintype.sum_prod_type, norm_mul, mul_pow, Finset.sum_mul_sum]

/-- The squared norm of a vector, cast to `ℂ`, is its Hermitian dot product with itself:
`∑ₓ ‖w x‖² = star w ⬝ᵥ w`. -/
private theorem sum_norm_sq_eq_dotProduct (w : d → ℂ) :
    ((∑ x, ‖w x‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
  push_cast
  simp [dotProduct, Complex.conj_mul']

/-- A unitary matrix preserves the Hermitian inner product: `⟨U a, U b⟩ = ⟨a, b⟩`, where
`⟨a, b⟩ = star a ⬝ᵥ b = ∑ₓ conj (a x) · b x`. [dW26, App. A.4] (Added in fill epoch E1; the
squared-norm statement below and the no-cloning proofs both use it.)

**Proof sketch.** `star (U a) ⬝ᵥ (U b) = star a ⬝ᵥ ((star U * U) b)` (`star_mulVec`,
`dotProduct_mulVec`, `vecMul_vecMul`), and `star U * U = 1` (`Matrix.mem_unitaryGroup_iff'`). -/
theorem inner_mulVec_of_mem_unitaryGroup [DecidableEq d] {U : Matrix d d ℂ} (hU : U ∈ 𝐔[d])
    (a b : d → ℂ) : star (U *ᵥ a) ⬝ᵥ (U *ᵥ b) = star a ⬝ᵥ b := by
  rw [Matrix.mem_unitaryGroup_iff'] at hU
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose, hU, vecMul_one]

/-- A unitary matrix preserves the squared norm of every vector: `∑ ‖(U v) x‖² = ∑ ‖v x‖²`.
[dW26, §1.2.3, App. A.4]

**Proof sketch.** Write the squared norm as `star v ⬝ᵥ v`. Then
`star (U v) ⬝ᵥ (U v) = star v ⬝ᵥ ((star U * U) v)`, and `star U * U = 1` for `U` in the
unitary group (`Matrix.mem_unitaryGroup_iff'`). -/
theorem sum_norm_sq_mulVec_of_mem_unitaryGroup [DecidableEq d] {U : Matrix d d ℂ}
    (hU : U ∈ 𝐔[d]) (v : d → ℂ) :
    ∑ x, ‖(U *ᵥ v) x‖ ^ 2 = ∑ x, ‖v x‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sum_norm_sq_eq_dotProduct, sum_norm_sq_eq_dotProduct, inner_mulVec_of_mem_unitaryGroup hU]

end Norms

/-! ### Pure states -/

/-- A pure state (ket) over a finite basis `d`: a vector `vec : d → ℂ` with
`∑ₓ ‖vec x‖² = 1`. [dW26, §1.2.1]; the structure and its field names follow [Physlib]. -/
@[ext]
structure Ket (d : Type*) [Fintype d] where
  /-- The amplitudes of the state in the basis `d`. -/
  vec : d → ℂ
  /-- The amplitudes have squared norm `1`. -/
  normalized' : ∑ x, ‖vec x‖ ^ 2 = 1

namespace Ket

variable {d d₁ d₂ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂]

/-- The basis state `|i⟩`: amplitude `1` at `i` and `0` elsewhere. [dW26, §1.2.1] -/
def basis [DecidableEq d] (i : d) : Ket d where
  vec j := if i = j then 1 else 0
  normalized' := sum_norm_sq_basisVec i

/-- The amplitude of `|i⟩` at `j` is `1` if `i = j` and `0` otherwise. -/
theorem basis_vec [DecidableEq d] (i j : d) :
    (basis i).vec j = if i = j then 1 else 0 := rfl

/-- The state `ψ` read through a relabelling `e : d₂ ≃ d₁` of its basis: the amplitude at `i`
is `ψ`'s amplitude at `e i`. Name and argument order follow [Physlib]. -/
def relabel (ψ : Ket d₁) (e : d₂ ≃ d₁) : Ket d₂ where
  vec i := ψ.vec (e i)
  normalized' := (sum_norm_sq_comp_equiv ψ.vec e).trans ψ.normalized'

/-- The amplitude of `ψ.relabel e` at `i` is `ψ.vec (e i)`. -/
theorem relabel_vec (ψ : Ket d₁) (e : d₂ ≃ d₁) (i : d₂) :
    (ψ.relabel e).vec i = ψ.vec (e i) := rfl

/-- The tensor product `ψ ⊗ φ` of two states, a state over the product basis with amplitude
`ψ i · φ j` at `(i, j)`. [dW26, App. A.6]; the name follows [Physlib]. -/
def prod (ψ : Ket d₁) (φ : Ket d₂) : Ket (d₁ × d₂) where
  vec p := ψ.vec p.1 * φ.vec p.2
  normalized' := by
    rw [sum_norm_sq_mul_prod, ψ.normalized', φ.normalized', one_mul]

/-- The amplitude of `ψ.prod φ` at `(i, j)` is `ψ.vec i * φ.vec j`. -/
theorem prod_vec (ψ : Ket d₁) (φ : Ket d₂) (p : d₁ × d₂) :
    (ψ.prod φ).vec p = ψ.vec p.1 * φ.vec p.2 := rfl

/-- The state `U ψ` obtained by applying the unitary `U` to `ψ`. [dW26, §1.2.3] -/
noncomputable def evolve [DecidableEq d] (U : 𝐔[d]) (ψ : Ket d) : Ket d where
  vec := (U : Matrix d d ℂ) *ᵥ ψ.vec
  normalized' := (sum_norm_sq_mulVec_of_mem_unitaryGroup U.2 ψ.vec).trans ψ.normalized'

/-- The amplitudes of `ψ.evolve U` are `U *ᵥ ψ.vec`. -/
theorem evolve_vec [DecidableEq d] (U : 𝐔[d]) (ψ : Ket d) :
    (ψ.evolve U).vec = (U : Matrix d d ℂ) *ᵥ ψ.vec := rfl

/-- Applying `U * V` is applying `V`, then `U`.

**Proof sketch.** `(U * V) *ᵥ v = U *ᵥ (V *ᵥ v)` (`Matrix.mulVec_mulVec`), then `Ket.ext`. -/
theorem evolve_mul [DecidableEq d] (U V : 𝐔[d]) (ψ : Ket d) :
    ψ.evolve (U * V) = (ψ.evolve V).evolve U := by
  ext x
  simp [evolve_vec, Matrix.mulVec_mulVec]

/-- Applying the identity does nothing.

**Proof sketch.** `1 *ᵥ v = v` (`Matrix.one_mulVec`), then `Ket.ext`. -/
theorem evolve_one [DecidableEq d] (ψ : Ket d) : ψ.evolve 1 = ψ := by
  ext x
  simp [evolve_vec]

/-- There is no state on an empty basis: the empty sum of squared norms is `0`, not `1`. This
distinguishes an empty basis from the one-element basis `Reg 0` (round-1 audit, sanity
statement 1).

**Proof sketch.** For a ket on an empty basis, `normalized'` says `0 = 1`
(`Finset.univ_eq_empty`, `Finset.sum_empty`). -/
theorem isEmpty_of_isEmpty [IsEmpty d] : IsEmpty (Ket d) :=
  ⟨fun ψ => by have := ψ.normalized'; simp at this⟩

/-- The zero-qubit register carries a state: the basis state of its unique basis element. -/
theorem nonempty_reg_zero : Nonempty (Ket (Reg 0)) := ⟨basis Fin.elim0⟩

end Ket

/-- `ψ ⊗ᵠ φ` is the tensor product `Ket.prod ψ φ`. Notation as in [Physlib]. -/
scoped infixl:100 " ⊗ᵠ " => Ket.prod

end Quantum
