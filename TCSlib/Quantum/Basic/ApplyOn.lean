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
* `Quantum.applyOn_mulVec_apply`, `Quantum.applyOn_wire_mulVec_apply`,
  `Quantum.applyOn_permMat_mulVec_apply` — the action on an arbitrary vector: in general, for a
  one-wire gate, and for a permutation gate (added in fill epoch E1).
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

/-! ### Reconstructing a register from its gate wires -/

/-- `AgreeOff w` is symmetric. -/
private theorem agreeOff_symm {w : Fin k ↪ Fin n} {y x : Reg n} (h : AgreeOff w y x) :
    AgreeOff w x y :=
  fun i hi => (h i hi).symm

/-- `AgreeOff w` is transitive. -/
private theorem agreeOff_trans {w : Fin k ↪ Fin n} {y z x : Reg n} (h₁ : AgreeOff w y z)
    (h₂ : AgreeOff w z x) : AgreeOff w y x :=
  fun i hi => (h₁ i hi).trans (h₂ i hi)

/-- Writing `u` on the wires `w` and copying `x` elsewhere, then reading the wires `w`, gives
back `u`. -/
private theorem extend_comp (w : Fin k ↪ Fin n) (u : Reg k) (x : Reg n) :
    Function.extend w u x ∘ w = u := by
  funext j
  exact w.injective.extend_apply u x j

/-- Writing `u` on the wires `w` and copying `x` elsewhere agrees with `x` off `w`. -/
private theorem agreeOff_extend (w : Fin k ↪ Fin n) (u : Reg k) (x : Reg n) :
    AgreeOff w (Function.extend w u x) x := by
  intro i hi
  exact Function.extend_apply' u x i (fun ⟨j, hj⟩ => hi j hj)

/-- A register agreeing with `x` off `w` is recovered from its values on `w` and from `x`: the
two maps of the bijection behind `applyOn_mul` are inverse. -/
private theorem extend_self {w : Fin k ↪ Fin n} {z x : Reg n} (h : AgreeOff w z x) :
    Function.extend w (z ∘ w) x = z := by
  funext i
  by_cases hi : ∃ j, w j = i
  · obtain ⟨j, rfl⟩ := hi
    exact w.injective.extend_apply (z ∘ w) x j
  · rw [Function.extend_apply' _ _ _ hi]
    exact (h i fun j hj => hi ⟨j, hj⟩).symm

/-- Registers that agree off `w` and on `w` are equal. -/
private theorem eq_of_agreeOff {w : Fin k ↪ Fin n} {y x : Reg n} (h : AgreeOff w y x)
    (hw : y ∘ w = x ∘ w) : y = x :=
  calc y = Function.extend w (y ∘ w) x := (extend_self h).symm
    _ = Function.extend w (x ∘ w) x := by rw [hw]
    _ = x := extend_self fun _ _ => rfl

/-! ### Algebraic properties -/

/-- Placing the identity on any wires gives the identity.

**Proof sketch.** Entry `(y, x)` is `[y ∘ w = x ∘ w]` when `y, x` agree off `w`, and `0`
otherwise; both cases together say `[y = x]`. -/
theorem applyOn_one (w : Fin k ↪ Fin n) : applyOn w (1 : Matrix (Reg k) (Reg k) ℂ) = 1 := by
  ext y x
  rw [applyOn_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : AgreeOff w y x
  · rw [if_pos h]
    by_cases hw : y ∘ w = x ∘ w
    · rw [if_pos hw, if_pos (eq_of_agreeOff h hw)]
    · rw [if_neg hw, if_neg (fun hyx => hw (by rw [hyx]))]
  · rw [if_neg h, if_neg (fun hyx => h (by subst hyx; exact fun _ _ => rfl))]

/-- A placed gate acts on a vector `v` by summing over the gate's own basis: the amplitude at `y`
is `∑ᵤ U (y ∘ w) u · v (y with u written on the wires w)`. This is a coordinate formula for an
arbitrary matrix `U` and vector `v`; it extends the placement of unitary gates in
[dW26, §2.1.2], which the formula does not need.

**Proof sketch.** Only registers `z` agreeing with `y` off `w` contribute to
`∑_z applyOn w U y z · v z`, and they correspond to `u : Reg k` through `z ↦ z ∘ w`, with inverse
"write `u` on `w`, copy `y` elsewhere" (`Function.extend`; `extend_comp`, `extend_self`). This
bijection is the key step; `applyOn_mul` is derived from this lemma. -/
theorem applyOn_mulVec_apply (w : Fin k ↪ Fin n) (U : Matrix (Reg k) (Reg k) ℂ) (v : Reg n → ℂ)
    (y : Reg n) :
    (applyOn w U *ᵥ v) y = ∑ u : Reg k, U (y ∘ w) u * v (Function.extend w u y) := by
  simp only [mulVec, dotProduct, applyOn_apply]
  have key : (∑ z, (if AgreeOff w y z then U (y ∘ w) (z ∘ w) else 0) * v z) =
      ∑ z ∈ Finset.univ.filter (fun z => AgreeOff w z y),
        (if AgreeOff w y z then U (y ∘ w) (z ∘ w) else 0) * v z := by
    refine (Finset.sum_filter_of_ne fun z _ hz => ?_).symm
    by_contra h
    exact hz (by rw [if_neg (fun h' => h (agreeOff_symm h')), zero_mul])
  rw [key]
  apply Finset.sum_nbij' (fun z => z ∘ w) (fun u => Function.extend w u y)
  · intros; exact Finset.mem_univ _
  · intro u _; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, agreeOff_extend w u y⟩
  · intro z hz; exact extend_self (Finset.mem_filter.1 hz).2
  · intro u _; exact extend_comp w u y
  · intro z hz
    rw [if_pos (agreeOff_symm (Finset.mem_filter.1 hz).2), extend_self (Finset.mem_filter.1 hz).2]

/-- Placing a product on wires `w` is the product of the placed factors:
`applyOn w (U V) = applyOn w U · applyOn w V`.

**Proof sketch.** Entry `(y, x)` of the right side is `applyOn w U` applied to column `x` of
`applyOn w V`, at `y`. By `applyOn_mulVec_apply` it is `∑_u U (y ∘ w) u · applyOn w V y_u x`, where
`y_u` is `y` with `u` written on the wires `w`. Now `y_u` reads `u` on `w` (`extend_comp`) and
agrees with `x` off `w` exactly when `y` does (`agreeOff_extend`). So the sum is
`∑_u U (y ∘ w) u · V u (x ∘ w)`, entry `(y ∘ w, x ∘ w)` of `U V`, when `y, x` agree off `w`, and
`0` otherwise. -/
theorem applyOn_mul (w : Fin k ↪ Fin n) (U V : Matrix (Reg k) (Reg k) ℂ) :
    applyOn w (U * V) = applyOn w U * applyOn w V := by
  ext y x
  have h := applyOn_mulVec_apply w U (fun z => applyOn w V z x) y
  simp only [mulVec, dotProduct] at h
  rw [Matrix.mul_apply, h]
  simp only [applyOn_apply, extend_comp]
  by_cases hyx : AgreeOff w y x
  · rw [if_pos hyx, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [if_pos (agreeOff_trans (agreeOff_extend w u y) hyx)]
  · rw [if_neg hyx]
    symm
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [if_neg (fun h => hyx (agreeOff_trans (agreeOff_symm (agreeOff_extend w u y)) h)), mul_zero]

/-- Placing commutes with adjoints: `(applyOn w U)ᴴ = applyOn w Uᴴ`.

**Proof sketch.** `AgreeOff w y x` is symmetric in `y, x`, and entry `(y, x)` of `Uᴴ` is
`conj (U x y)`. -/
theorem applyOn_conjTranspose (w : Fin k ↪ Fin n) (U : Matrix (Reg k) (Reg k) ℂ) :
    (applyOn w U)ᴴ = applyOn w Uᴴ := by
  ext y x
  simp only [conjTranspose_apply, applyOn_apply]
  by_cases h : AgreeOff w x y
  · rw [if_pos h, if_pos (agreeOff_symm h)]
  · rw [if_neg h, if_neg (fun h' => h (agreeOff_symm h')), star_zero]

/-- Placing a unitary on any wires gives a unitary.

**Proof sketch.** `(applyOn w U)ᴴ · applyOn w U = applyOn w (Uᴴ U) = applyOn w 1 = 1`, by
`applyOn_conjTranspose`, `applyOn_mul` and `applyOn_one`. -/
theorem applyOn_mem_unitaryGroup (w : Fin k ↪ Fin n) {U : Matrix (Reg k) (Reg k) ℂ}
    (hU : U ∈ 𝐔[Reg k]) : applyOn w U ∈ 𝐔[Reg n] := by
  rw [mem_unitaryGroup_iff'] at hU ⊢
  rw [star_eq_conjTranspose, applyOn_conjTranspose, ← applyOn_mul, ← star_eq_conjTranspose, hU,
    applyOn_one]

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
  ext y x
  rw [applyOn_apply, if_pos (show AgreeOff _ y x from fun i hi => absurd rfl (hi i))]
  rfl

/-- The product of two operators on disjoint wires, entrywise: it is
`U₁ (y ∘ w₁) (x ∘ w₁) · U₂ (y ∘ w₂) (x ∘ w₂)` when `y` and `x` agree off both ranges, and `0`
otherwise. The only intermediate register that can contribute agrees with `x` on `w₁`'s range and
with `y` elsewhere.

**Proof sketch.** Let `z*` be `y` on `w₂`'s range and `x` elsewhere. Then `z* ∘ w₁ = x ∘ w₁`
(the ranges are disjoint), `z* ∘ w₂ = y ∘ w₂`, `z*` agrees with `x` off `w₂`, and `z*` agrees with
`y` off `w₁` exactly when `y` and `x` agree off both ranges. So the term at `z*` is the stated
expression. Any other `z` with a nonzero term would agree with `y` off `w₁` and with `x` off `w₂`,
which forces `z = z*` wire by wire (`Finset.sum_eq_single`). -/
private theorem applyOn_mul_applyOn_of_disjoint (w₁ : Fin k₁ ↪ Fin n) (w₂ : Fin k₂ ↪ Fin n)
    (hd : ∀ j₁ j₂, w₁ j₁ ≠ w₂ j₂)
    (U₁ : Matrix (Reg k₁) (Reg k₁) ℂ) (U₂ : Matrix (Reg k₂) (Reg k₂) ℂ) (y x : Reg n) :
    (applyOn w₁ U₁ * applyOn w₂ U₂) y x =
      if (∀ i, (∀ j, w₁ j ≠ i) → (∀ j, w₂ j ≠ i) → y i = x i) then
        U₁ (y ∘ w₁) (x ∘ w₁) * U₂ (y ∘ w₂) (x ∘ w₂) else 0 := by
  -- The candidate intermediate register `z*` of the sketch, and its four properties.
  set zs : Reg n := fun i => if ∃ j, w₂ j = i then y i else x i with hzs
  have hz1 : zs ∘ w₁ = x ∘ w₁ := by
    funext j; simp only [Function.comp, hzs]
    rw [if_neg (fun ⟨j', hj'⟩ => hd j j' hj'.symm)]
  have hz2 : zs ∘ w₂ = y ∘ w₂ := by
    funext j; simp only [Function.comp, hzs]; rw [if_pos ⟨j, rfl⟩]
  have hA2 : AgreeOff w₂ zs x := by
    intro i hi; simp only [hzs]; rw [if_neg (fun ⟨j, hj⟩ => hi j hj)]
  have hA1 : AgreeOff w₁ y zs ↔ ∀ i, (∀ j, w₁ j ≠ i) → (∀ j, w₂ j ≠ i) → y i = x i := by
    constructor
    · intro h i h1 h2
      have := h i h1; simp only [hzs] at this; rwa [if_neg (fun ⟨j, hj⟩ => h2 j hj)] at this
    · intro h i h1
      simp only [hzs]
      by_cases hi : ∃ j, w₂ j = i
      · rw [if_pos hi]
      · rw [if_neg hi]; exact h i h1 (fun j hj => hi ⟨j, hj⟩)
  -- The sum over intermediate registers has only the term at `zs`.
  rw [Matrix.mul_apply, Finset.sum_eq_single zs]
  · -- The term at `zs` is the stated expression.
    simp only [applyOn_apply]
    rw [if_pos hA2, hz1, hz2]
    by_cases hc : ∀ i, (∀ j, w₁ j ≠ i) → (∀ j, w₂ j ≠ i) → y i = x i
    · rw [if_pos (hA1.2 hc), if_pos hc]
    · rw [if_neg (fun h => hc (hA1.1 h)), if_neg hc, zero_mul]
  · -- Any other `z` with a nonzero term would equal `zs` wire by wire.
    intro z _ hz
    simp only [applyOn_apply]
    by_cases h1 : AgreeOff w₁ y z
    · by_cases h2 : AgreeOff w₂ z x
      · exfalso; apply hz; funext i; simp only [hzs]
        by_cases hi : ∃ j, w₂ j = i
        · rw [if_pos hi]; obtain ⟨j, rfl⟩ := hi
          exact (h1 (w₂ j) (fun j' hj' => hd j' j hj')).symm
        · rw [if_neg hi]; exact h2 i (fun j hj => hi ⟨j, hj⟩)
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Operators on disjoint sets of wires commute. [NC10, §4.5]

**Proof sketch.** Both products have entry `(y, x)` equal to
`U₁ (y ∘ w₁) (x ∘ w₁) · U₂ (y ∘ w₂) (x ∘ w₂)` when `y, x` agree off the union of the two ranges,
and `0` otherwise. Each side reduces to this: its sum over intermediate registers `z` has at
most one nonzero term, at the unique `z` satisfying the outside-wire constraints (the term itself
may vanish; round-2 audit, finding 2). In `applyOn w₁ U₁ * applyOn w₂ U₂`, that `z` agrees with
`x` on `w₁`'s range and with `y` on `w₂`'s; in the reversed product it agrees with `y` on `w₁`'s
range and with `x` on `w₂`'s. Off both ranges it is the common value of `y` and `x`. The two
scalar products are then equal because complex multiplication commutes (round-1 audit,
finding 4). -/
theorem applyOn_commute_of_disjoint (w₁ : Fin k₁ ↪ Fin n) (w₂ : Fin k₂ ↪ Fin n)
    (h : Disjoint (Set.range w₁) (Set.range w₂))
    (U₁ : Matrix (Reg k₁) (Reg k₁) ℂ) (U₂ : Matrix (Reg k₂) (Reg k₂) ℂ) :
    Commute (applyOn w₁ U₁) (applyOn w₂ U₂) := by
  have hd : ∀ j₁ j₂, w₁ j₁ ≠ w₂ j₂ := fun j₁ j₂ e =>
    Set.disjoint_left.1 h ⟨j₁, rfl⟩ ⟨j₂, e.symm⟩
  show applyOn w₁ U₁ * applyOn w₂ U₂ = applyOn w₂ U₂ * applyOn w₁ U₁
  ext y x
  rw [applyOn_mul_applyOn_of_disjoint w₁ w₂ hd,
    applyOn_mul_applyOn_of_disjoint w₂ w₁ (fun a b e => hd b a e.symm)]
  by_cases hc : ∀ i, (∀ j, w₁ j ≠ i) → (∀ j, w₂ j ≠ i) → y i = x i
  · rw [if_pos hc, if_pos (fun i h2 h1 => hc i h1 h2), mul_comm]
  · rw [if_neg hc, if_neg (fun hc' => hc (fun i h1 h2 => hc' i h2 h1))]

/-- Two registers agree off the first `k` wires iff they agree on the last `m`. -/
private theorem agreeOff_castAddEmb_iff (m : ℕ) (y x : Reg (k + m)) :
    AgreeOff (Fin.castAddEmb m) y x ↔
      (fun i => y (Fin.natAdd k i)) = (fun i => x (Fin.natAdd k i)) := by
  constructor
  · intro h; funext i
    apply h (Fin.natAdd k i)
    intro j hj
    have := congrArg Fin.val hj; simp at this; omega
  · intro H i hi
    by_cases hik : (i : ℕ) < k
    · exact absurd (Fin.ext rfl) (hi ⟨i, hik⟩)
    · have : i = Fin.natAdd k ⟨i - k, by omega⟩ := Fin.ext (by simp; omega)
      rw [this]; exact congrFun H _

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
  ext y x
  simp only [reindex_apply, submatrix_apply, regAppendEquiv_symm_apply, kroneckerMap_apply,
    applyOn_apply, Matrix.one_apply]
  by_cases hA : AgreeOff (Fin.castAddEmb m) y x
  · rw [if_pos hA, if_pos ((agreeOff_castAddEmb_iff m y x).1 hA), mul_one]; rfl
  · rw [if_neg hA, if_neg (fun h => hA ((agreeOff_castAddEmb_iff m y x).2 h)), mul_zero]

/-! ### Action on basis states -/

/-- The image of a basis state: `applyOn w U |x⟩` has amplitude `U (y ∘ w) (x ∘ w)` at each `y`
agreeing with `x` off `w`, and `0` elsewhere.

**Proof sketch.** Column `x` of a matrix is its product with `|x⟩`
(`Matrix.mulVec_single`-style computation), and column `x` of `applyOn w U` is read off
`applyOn_apply`. -/
theorem applyOn_mulVec_basis (w : Fin k ↪ Fin n) (U : Matrix (Reg k) (Reg k) ℂ) (x : Reg n) :
    applyOn w U *ᵥ (Ket.basis x).vec =
      fun y => if AgreeOff w y x then U (y ∘ w) (x ∘ w) else 0 := by
  ext y
  simp [mulVec, dotProduct, applyOn_apply, Ket.basis_vec]

/-- With no wires (`k = 0`), `applyOn` scales the identity by the single entry of the `1 × 1`
matrix `U`: a zero-qubit operator acts as a global scalar (round-1 audit, sanity statement 2).
`U` need not be unitary.

**Proof sketch.** Every wire is outside the (empty) range, so `AgreeOff w y x` says `y = x`, and
`y ∘ w = x ∘ w` is the unique element of `Reg 0`. -/
theorem applyOn_of_fin_zero (w : Fin 0 ↪ Fin n) (U : Matrix (Reg 0) (Reg 0) ℂ) :
    applyOn w U = U Fin.elim0 Fin.elim0 • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  ext y x
  rw [applyOn_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have h0 : ∀ z : Reg n, z ∘ w = Fin.elim0 := fun z => funext fun j => j.elim0
  by_cases h : y = x
  · rw [if_pos (by subst h; exact fun _ _ => rfl), if_pos h, h0, h0, mul_one]
  · rw [if_neg (fun h' => h (funext fun i => h' i (fun j => j.elim0))), if_neg h, mul_zero]

/-- A permutation gate placed on wires `w` maps `|x⟩` to the basis state that holds `σ (x ∘ w)`
on the wires `w` and agrees with `x` elsewhere. -/
private theorem applyOn_permMat_mulVec_basis (w : Fin k ↪ Fin n) (σ : Equiv.Perm (Reg k))
    (x : Reg n) :
    applyOn w (permMat σ) *ᵥ (Ket.basis x).vec =
      (Ket.basis (Function.extend w (σ (x ∘ w)) x)).vec := by
  rw [applyOn_mulVec_basis]
  funext y
  simp only [Ket.basis_vec, permMat_apply]
  by_cases hA : AgreeOff w y x
  · rw [if_pos hA]
    by_cases hy : y ∘ w = σ (x ∘ w)
    · rw [if_pos hy, if_pos (by rw [← hy, extend_self hA])]
    · rw [if_neg hy, if_neg (fun he => hy (by rw [← he, extend_comp]))]
  · rw [if_neg hA, if_neg (fun he => hA (by rw [← he]; exact agreeOff_extend w _ x))]

/-- The embedding `Fin 1 ↪ Fin n` naming the single wire `i`. -/
def wire (i : Fin n) : Fin 1 ↪ Fin n := ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩

/-- `wire i` sends the gate's only wire to `i`. -/
theorem wire_apply (i : Fin n) (j : Fin 1) : wire i j = i := rfl

/-! ### Action on arbitrary vectors -/

/-- Writing a one-qubit register `u` on the single wire `i` of `y` is updating `y` at `i` to
`u 0`. -/
private theorem extend_wire (i : Fin n) (u : Reg 1) (y : Reg n) :
    Function.extend (wire i) u y = Function.update y i (u 0) := by
  funext j
  by_cases hj : j = i
  · subst hj
    exact (wire j).injective.extend_apply _ y 0 |>.trans (by simp)
  · rw [Function.extend_apply' _ _ _ (fun ⟨b, hb⟩ => hj (by rw [← hb, wire_apply])),
      Function.update_of_ne hj]

/-- A one-wire operator placed on wire `i` acts on a vector by a two-term sum over the input bit
`a` on wire `i`: the amplitude at `y` is `∑ₐ U (y i) a · v (y with wire i set to a)`, where `y i`
is the output bit. A coordinate formula for an arbitrary matrix `U` and vector `v`, extending the
one-qubit gates of [dW26, §1.4].

**Proof sketch.** `applyOn_mulVec_apply`, with `Reg 1 ≃ Qubit` and the fact that writing `u` on
the single wire `i` is `Function.update y i (u 0)` (`extend_wire`). -/
theorem applyOn_wire_mulVec_apply (i : Fin n) (U : Matrix (Reg 1) (Reg 1) ℂ) (v : Reg n → ℂ)
    (y : Reg n) :
    (applyOn (wire i) U *ᵥ v) y =
      ∑ a : Qubit, U (fun _ => y i) (fun _ => a) * v (Function.update y i a) := by
  rw [applyOn_mulVec_apply, ← (Equiv.funUnique (Fin 1) Qubit).symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [extend_wire]
  rfl

/-- A permutation gate placed on wires `w` relabels the amplitudes: the amplitude at `y` is `v`'s
amplitude at the register holding `σ⁻¹ (y ∘ w)` on the wires `w` and agreeing with `y` elsewhere.

**Proof sketch.** In `applyOn_mulVec_apply`, `permMat σ (y ∘ w) u` is `1` exactly when
`u = σ⁻¹ (y ∘ w)` and `0` otherwise, so only that term survives (`Finset.sum_eq_single`). -/
theorem applyOn_permMat_mulVec_apply (w : Fin k ↪ Fin n) (σ : Equiv.Perm (Reg k)) (v : Reg n → ℂ)
    (y : Reg n) :
    (applyOn w (permMat σ) *ᵥ v) y = v (Function.extend w (σ.symm (y ∘ w)) y) := by
  rw [applyOn_mulVec_apply]
  simp only [permMat_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm (y ∘ w))]
  · rw [if_pos (by simp)]
  · intro u _ hu
    rw [if_neg (fun h => hu (by rw [h, Equiv.symm_apply_apply]))]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Sanity check for the definition of `applyOn`: the NOT gate placed on wire `i` maps the
basis state `|x⟩` to `|x with wire i flipped⟩`. [dW26, §1.4]

**Proof sketch.** A placed permutation gate maps `|x⟩` to the basis state holding `σ (x ∘ w)` on
the wires `w` and agreeing with `x` elsewhere (`applyOn_permMat_mulVec_basis`). For `X` on
`wire i`, that state is `x` with wire `i` changed to `x i + 1`, which is `flipAt i x`. -/
theorem applyOn_wire_X_mulVec_basis (i : Fin n) (x : Reg n) :
    applyOn (wire i) (Gate.X : Matrix (Reg 1) (Reg 1) ℂ) *ᵥ (Ket.basis x).vec =
      (Ket.basis (flipAt i x)).vec := by
  rw [Gate.X_coe, applyOn_permMat_mulVec_basis]
  congr 2
  rw [extend_wire, flipAt_eq]
  simp [flipAt_eq, wire_apply]

/-- The embedding `Fin 2 ↪ Fin 3` sending gate wire `0` to register wire `2` and gate wire `1`
to register wire `0`: a reversed, non-contiguous placement, used as a sanity check. -/
def wires20 : Fin 2 ↪ Fin 3 := ⟨![2, 0], by decide⟩

/-- `wires20` sends `j` to `![2, 0] j`. -/
theorem wires20_apply (j : Fin 2) : wires20 j = ![2, 0] j := rfl

/-- Sanity check for reversed, non-contiguous placement: `CNOT` placed with its control on
register wire `2` and its target on register wire `0` maps `|x⟩` to the basis state with wire `0`
replaced by `x 0 + x 2`, all other wires unchanged (round-1 audit, sanity statement 3; on the
input `011` the output is `111`).

**Proof sketch.** By `applyOn_permMat_mulVec_basis`, the image is the basis state holding
`cnotMap (x 2, x 0) = (x 2, x 0 + x 2)` on wires `(2, 0)` and `x 1` on wire `1`. Check it wire by
wire against `Function.update x 0 (x 0 + x 2)`. -/
theorem applyOn_wires20_CNOT_mulVec_basis (x : Reg 3) :
    applyOn wires20 (Gate.CNOT : Matrix (Reg 2) (Reg 2) ℂ) *ᵥ (Ket.basis x).vec =
      (Ket.basis (Function.update x 0 (x 0 + x 2))).vec := by
  rw [Gate.CNOT_coe, applyOn_permMat_mulVec_basis]
  congr 2
  funext j
  fin_cases j
  · rw [show ((⟨0, by decide⟩ : Fin 3)) = wires20 1 from rfl, wires20.injective.extend_apply]
    simp [cnotMap_eq, wires20_apply]
  · rw [Function.extend_apply' _ _ _ (by decide)]
    simp
  · rw [show ((⟨2, by decide⟩ : Fin 3)) = wires20 0 from rfl, wires20.injective.extend_apply]
    simp [cnotMap_eq, wires20_apply]

end Quantum
