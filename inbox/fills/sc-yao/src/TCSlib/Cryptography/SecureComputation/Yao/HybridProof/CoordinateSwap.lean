/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Re-randomizing a partial family of seed coordinates

An unchanged control value chooses a partial matching between full-seed coordinates and
independent challenge coordinates. Swapping each matched pair is an involution. Unmatched
full coordinates and unused padded challenge slots remain unchanged. Values are never
compared, so repeated actual key or nonce values need no separate treatment.

## Main definitions

* `CoordinateSwap.swap`: the simultaneous matched-coordinate exchange.
* `CoordinateSwap.equiv`: its self-inverse joint-seed bijection.

## Main results

* `CoordinateSwap.swap_involutive`: the exchange is its own inverse.
* `acceptProb_swap`, `acceptProb_fill`: exact generic and transported acceptance laws.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (independent inactive-key and encryption-coin resampling).

This is a technical coordinate formulation for that simulation. It reuses the existing
finite-probability relabeling contracts rather than proving a new counting identity.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap

variable {P I J V : Type*}

/-- Exchange every full coordinate selected by `pick` with its challenge coordinate,
using `place` for the reverse direction. The control value stays fixed, and `none` retains
that side's original value, including every unused padded challenge slot. -/
@[simps (config := { isSimp := false })]
def swap (pick : P → I → Option J) (place : P → J → Option I)
    (s : (P × (I → V)) × (J → V)) : (P × (I → V)) × (J → V) :=
  ((s.1.1, fun i => (pick s.1.1 i).elim (s.1.2 i) (fun j => s.2 j)),
    fun j => (place s.1.1 j).elim (s.2 j) (fun i => s.1.2 i))

/-- `swap pick place s` retains `s.control`, exchanges matched full/challenge coordinates,
and retains a side's original coordinate when its selector returns `none`. -/
theorem swap_eq (pick : P → I → Option J) (place : P → J → Option I)
    (s : (P × (I → V)) × (J → V)) :
    swap pick place s =
      ((s.1.1, fun i => (pick s.1.1 i).elim (s.1.2 i) (fun j => s.2 j)),
        fun j => (place s.1.1 j).elim (s.2 j) (fun i => s.1.2 i)) := rfl

/-- If `pick p i = some j` exactly when `place p j = some i`, the simultaneous exchange
is an involution. No distinctness or decidable equality of coordinate values is required.

**Proof sketch.** The control value is unchanged. At a selected full coordinate, the first
exchange reads the challenge coordinate, and the matching condition makes the second read
its original full value. An unselected coordinate is retained twice. The same two cases
on a challenge coordinate recover its original value; this includes every padded slot
whose reverse selector is `none`. Function and product extensionality assemble the result. -/
theorem swap_involutive (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i) :
    Function.Involutive (swap pick place : ((P × (I → V)) × (J → V)) → _) := by
  rintro ⟨⟨p, full⟩, challenge⟩
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext i
      cases h : pick p i with
      | none => simp only [swap_eq, h, Option.elim_none]
      | some j =>
        have h' := (hmatch p i j).mp h
        simp only [swap_eq, h, h', Option.elim_some]
  · funext j
    cases h : place p j with
    | none => simp only [swap_eq, h, Option.elim_none]
    | some i =>
      have h' := (hmatch p i j).mpr h
      simp only [swap_eq, h, h', Option.elim_some]

/-- The matched-coordinate exchange is a bijection of the joint full/challenge seed space.
Its inverse is the same exchange; the control value remains fixed. -/
@[simps (config := { isSimp := false }) apply symm_apply]
def equiv (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i) :
    ((P × (I → V)) × (J → V)) ≃ ((P × (I → V)) × (J → V)) where
  toFun := swap pick place
  invFun := swap pick place
  left_inv := swap_involutive pick place hmatch
  right_inv := swap_involutive pick place hmatch

/-- Applying `equiv pick place hmatch` is exactly `swap pick place`. -/
theorem equiv_apply_eq (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i)
    (s : (P × (I → V)) × (J → V)) :
    equiv pick place hmatch s = swap pick place s := rfl

/-- Applying the inverse of `equiv pick place hmatch` is the same `swap pick place`. -/
theorem equiv_symm_apply_eq (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i)
    (s : (P × (I → V)) × (J → V)) :
    (equiv pick place hmatch).symm s = swap pick place s := rfl

/-- Replacing the matched coordinates of an independent uniform full seed by uniform
challenge coordinates preserves every sampler acceptance probability. Unmatched challenge
slots may be padded, and coordinate values may repeat. Only the full coordinate spaces need
finite enumerations; the control and address types are not separately enumerated.
[PS10, Theorem 163.7]

**Proof sketch.** Relabel the joint uniform sample by the proved exchange bijection.
The sampler then sees just the original full-seed component. Remove its independent unused
challenge component with the existing ignored-coordinate probability contract. -/
theorem acceptProb_swap [Fintype (P × (I → V))] [Fintype (J → V)]
    [Nonempty (J → V)] {γ ρ : Type*} [Fintype ρ]
    (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i)
    (X : (P × (I → V)) → γ) (D : γ → ρ → Bool) :
    acceptProb (fun s : (P × (I → V)) × (J → V) => X (swap pick place s).1) D =
      acceptProb X D := by
  have h := acceptProb_comp_equiv (equiv pick place hmatch)
    (fun s : (P × (I → V)) × (J → V) => X s.1) D
  simp only [equiv_apply_eq] at h
  exact h.trans (acceptProb_fst X D)

/-- A concrete fill preserves the full seed's acceptance law when coordinate equivalences
identify it with the matched exchange. The challenge may have any equivalent finite shape,
including a key paired with padded nonce slots. [PS10, Theorem 163.7]

**Proof sketch.** Relabel the concrete full/challenge product by its two coordinate
bijections. The supplied fill equation identifies its full output with the first component
of the generic exchange. Apply the proved exchange law, then relabel the full coordinates
back to the original seed type. All probability steps use existing equivalence contracts. -/
theorem acceptProb_fill [Fintype P] [Fintype I] [Fintype J] [Fintype V]
    [DecidableEq I] [DecidableEq J]
    {S T γ ρ : Type*} [Fintype S] [Fintype T] [Nonempty T] [Fintype ρ]
    (pick : P → I → Option J) (place : P → J → Option I)
    (hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i)
    (seedEquiv : S ≃ (P × (I → V))) (challengeEquiv : T ≃ (J → V))
    (fill : S → T → S)
    (hfill : ∀ s c, seedEquiv (fill s c) =
      (swap pick place (seedEquiv s, challengeEquiv c)).1)
    (X : S → γ) (D : γ → ρ → Bool) :
    acceptProb (fun z : S × T => X (fill z.1 z.2)) D = acceptProb X D := by
  letI : Nonempty (J → V) := Nonempty.map challengeEquiv (inferInstance : Nonempty T)
  have hRelabel := acceptProb_comp_equiv (seedEquiv.prodCongr challengeEquiv)
    (fun w : (P × (I → V)) × (J → V) => X (seedEquiv.symm (swap pick place w).1)) D
  have hPoint : (fun z : S × T => X (fill z.1 z.2)) =
      (fun z => X (seedEquiv.symm
        (swap pick place ((seedEquiv.prodCongr challengeEquiv) z)).1)) := by
    funext z
    rw [Equiv.prodCongr_apply, Prod.map_apply', ← hfill z.1 z.2, Equiv.symm_apply_apply]
  rw [hPoint]
  exact hRelabel.trans ((acceptProb_swap pick place hmatch
    (fun w => X (seedEquiv.symm w)) D).trans (acceptProb_comp_equiv seedEquiv.symm X D))

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoordinateSwap
