/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
import TCSlib.Cryptography.Pairing.MatrixDH.FiniteLinear
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The raw simulator for the linear PHFE building block

The simulator uses the supplied source-group leakage directly. Its partial garbling is
computed at scalar value zero and multiplied by the supplied group value only at the
distinguished coordinate. All remaining operations are known scalar powers and products.

Setup samples an unconditioned uniform three-by-two matrix and an independent column.
Their transposed augmentation is inverted by Mathlib's total matrix inverse. On a singular
matrix this inverse is zero, so the simulator has an explicit total behavior on that event.
The exact failure probability is retained, rather than the printed `1/p` approximation.

## Main definitions

* `Wee20.Linear.groupPGStar`: simulated partial garbling from a group-valued allowed value.
* `Wee20.Linear.basisMatrix`, `SimState`, `SimSetupDraw`, `SimKeyDraw`: simulator data.
* `Wee20.Linear.simSetupCore`, `simEncCore`, `simKeyCore`: the explicit simulator algorithms.
* `Wee20.Linear.simSetup`, `simEnc`, `simKey`: exact laws of those algorithms.
* `Wee20.Linear.rankSlack`, `linearSlack`: exact full-rank failure terms.

## Main results

* `combineRows_reconstruct`: arbitrary source-group rows from a known inverse basis.

* `Wee20.Linear.groupPGStar_lift`: the group algorithm agrees with scalar partial garbling
  whenever its allowed group value is a known scalar power.
* `Wee20.Linear.simSetupCore_singular`: the singular branch uses the zero inverse.
* `Wee20.Linear.simSetup_fullRank_prob`: the exact probability of the good setup event.

This is an internal raw simulator. Its efficiency enters through the outer construction's
uniform targets; no efficient simulator interface is instantiated in this module.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §4.2, p. 10, Simulator and
  (12); Appendix B, pp. 12–14, Lemmas 2–5.
* [AGW20] M. Abdalla, J. Gong, and H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, CRYPTO 2020; full version, Cryptology ePrint Archive 2020/762,
  Lemma 2, p. 12, Appendix A, (30)–(32), pp. 37–38.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
open scoped Matrix

/-- Compute simulated partial garbling from the source-group allowed value. Start with
scalar value zero and multiply the allowed value at `m0`
[Wee20, §4.2, p. 10, KeyGen*; AGW20, Appendix A, (30)–(32), pp. 37–38]. -/
def groupPGStar (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (mu : pp.group.G)
    (t : (PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ)) → ZMod pp.group.order) :
    (Fin (n'.eval κ) ⊕ PG.MIdx κ pp.orderParam f) → pp.group.G :=
  let p0 := PG.pgbStar κ pp.orderParam f x 0 t
  Sum.elim (fun j => pp.generator ^ (p0 (Sum.inl j)).val)
    (fun u => pp.generator ^ (p0 (Sum.inr u)).val *
      if u = PG.m0 κ pp.orderParam f then mu else 1)

/-- The group garbling has the canonical zero-value exponents and one allowed-value factor. -/
theorem groupPGStar_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (mu : pp.group.G)
    (t : (PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ)) → ZMod pp.group.order) :
    groupPGStar G PG κ pp f x mu t =
      let p0 := PG.pgbStar κ pp.orderParam f x 0 t
      Sum.elim (fun j => pp.generator ^ (p0 (Sum.inl j)).val)
        (fun u => pp.generator ^ (p0 (Sum.inr u)).val *
          if u = PG.m0 κ pp.orderParam f then mu else 1) := rfl

/-- With a known scalar allowed value, group partial garbling is precisely its implicit
representation [Wee20, §4.2, p. 10; AGW20, Appendix A, (30), p. 37].

**Proof sketch.** Read `groupPGStar_eq`, `PG.pgbStar_eq` and the canonical block readers.
At the distinguished coordinate apply the source-group additive exponent law; elsewhere
the extra scalar is zero. The first block is unchanged. -/
theorem groupPGStar_lift (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (mu : ZMod pp.group.order)
    (t : (PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ)) → ZMod pp.group.order) :
    groupPGStar G PG κ pp f x (pp.generator ^ mu.val) t =
      pp.group.expVec pp.generator (PG.pgbStar κ pp.orderParam f x mu t) := by
  rw [groupPGStar_eq]
  funext i
  cases i with
  | inl j =>
      simp only [Sum.elim_inl, pp.group.expVec_apply, PG.pgbStar_eq,
        PartialGarbling.pgbStarCore_inl]
  | inr u =>
      simp only [Sum.elim_inr, pp.group.expVec_apply, PG.pgbStar_eq,
        PartialGarbling.pgbStarCore_inr]
      by_cases h : u = PG.m0 κ pp.orderParam f
      · simp only [if_pos h, add_zero]
        exact (pp.group.pow_val_add pp.generator _ _).symm
      · simp only [if_neg h, add_zero, mul_one]

/-- The simulator's basis matrix is `(A|c)^T` with the final row supplied by `c`
[Wee20, §4.2, p. 10, Setup*]. -/
def basisMatrix (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ)
    (A : Matrix (Fin 3) (Fin 2) (ZMod pp.group.order))
    (c : Fin 3 → ZMod pp.group.order) : Matrix (Fin 3) (Fin 3) (ZMod pp.group.order) :=
  fun i j => Fin.snoc (α := fun _ => ZMod pp.group.order) (fun a : Fin 2 => A j a) (c j) i

/-- Each column of the transposed augmentation appends its `c` entry after the two `A` entries. -/
theorem basisMatrix_eq (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ)
    (A : Matrix (Fin 3) (Fin 2) (ZMod pp.group.order)) (c : Fin 3 → ZMod pp.group.order) :
    basisMatrix G κ pp A c = fun i j => Fin.snoc (α := fun _ => ZMod pp.group.order) (fun a : Fin 2
      => A j a) (c j) i := rfl

/-- Π's simulator retains the scalar public-key masks, ideal ciphertext masks and inverse
basis [Wee20, §4.2, p. 10, Setup*]. The inverse is total, including singular setups. -/
structure SimState (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- The three-by-two public-key basis. -/
  A : Matrix (Fin 3) (Fin 2) (ZMod pp.group.order)
  /-- The private-input mask. -/
  W : Matrix (Fin 3) (Fin (zDim.eval κ)) (ZMod pp.group.order)
  /-- The public-variable mask. -/
  U : Matrix (Fin 3) (Fin (ℓ.eval κ) × Fin 2) (ZMod pp.group.order)
  /-- The constant mask. -/
  V : Matrix (Fin 3) (Fin 2) (ZMod pp.group.order)
  /-- The ideal three-coordinate ciphertext mask. -/
  c : Fin 3 → ZMod pp.group.order
  /-- The ideal private-input ciphertext mask. -/
  w : Fin (zDim.eval κ) → ZMod pp.group.order
  /-- The ideal public-input ciphertext mask. -/
  v : Fin 2 → ZMod pp.group.order
  /-- The total inverse of the transposed augmentation. -/
  basisInv : Matrix (Fin 3) (Fin 3) (ZMod pp.group.order)

/-- Simulator setup draws `A,c,W,U,V,w,v` independently and uniformly
[Wee20, §4.2, p. 10, Setup*]. -/
abbrev SimSetupDraw (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :=
  Matrix (Fin 3) (Fin 2) (ZMod pp.group.order) ×
    (Fin 3 → ZMod pp.group.order) ×
    Matrix (Fin 3) (Fin (zDim.eval κ)) (ZMod pp.group.order) ×
    Matrix (Fin 3) (Fin (ℓ.eval κ) × Fin 2) (ZMod pp.group.order) ×
    Matrix (Fin 3) (Fin 2) (ZMod pp.group.order) ×
    (Fin (zDim.eval κ) → ZMod pp.group.order) × (Fin 2 → ZMod pp.group.order)

/-- The simulator draw is exactly its seven independent scalar blocks. -/
theorem simSetupDraw_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) :
    SimSetupDraw G ℓ zDim κ pp =
      (Matrix (Fin 3) (Fin 2) (ZMod pp.group.order) ×
        (Fin 3 → ZMod pp.group.order) ×
        Matrix (Fin 3) (Fin (zDim.eval κ)) (ZMod pp.group.order) ×
        Matrix (Fin 3) (Fin (ℓ.eval κ) × Fin 2) (ZMod pp.group.order) ×
        Matrix (Fin 3) (Fin 2) (ZMod pp.group.order) ×
        (Fin (zDim.eval κ) → ZMod pp.group.order) × (Fin 2 → ZMod pp.group.order)) := rfl

instance instSimSetupDrawFinite (G : BilinearGen) (ℓ z : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    Fintype (SimSetupDraw G ℓ z κ pp) := inferInstance

instance instSimSetupDrawNonempty (G : BilinearGen) (ℓ z : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
  :
    Nonempty (SimSetupDraw G ℓ z κ pp) := inferInstance

/-- Simulator setup computes the public key and the total inverse basis
[Wee20, §4.2, p. 10, Setup*]. Unlike the source's implicit full-rank proviso, singular
inputs are defined: Mathlib's inverse is zero when the determinant is not a unit. -/
noncomputable def simSetupCore (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (ω : SimSetupDraw G ℓ zDim κ pp) :
    MPK G ℓ zDim κ pp × SimState G ℓ zDim κ pp :=
  let A := ω.1
  let c := ω.2.1
  let W := ω.2.2.1
  let U := ω.2.2.2.1
  let V := ω.2.2.2.2.1
  let w := ω.2.2.2.2.2.1
  let v := ω.2.2.2.2.2.2
  (⟨pp.group.expMat pp.generator Aᵀ, pp.group.expMat pp.generator (Aᵀ * W),
    pp.group.expMat pp.generator (Aᵀ * U), pp.group.expMat pp.generator (Aᵀ * V)⟩,
    ⟨A, W, U, V, c, w, v, (basisMatrix G κ pp A c)⁻¹⟩)

/-- Simulator setup is the displayed public exponentiation and total inverse construction. -/
theorem simSetupCore_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (ω : SimSetupDraw G ℓ zDim κ pp) :
    simSetupCore G ℓ zDim κ pp ω =
      let A := ω.1
      let c := ω.2.1
      let W := ω.2.2.1
      let U := ω.2.2.2.1
      let V := ω.2.2.2.2.1
      let w := ω.2.2.2.2.2.1
      let v := ω.2.2.2.2.2.2
      (⟨pp.group.expMat pp.generator Aᵀ, pp.group.expMat pp.generator (Aᵀ * W),
        pp.group.expMat pp.generator (Aᵀ * U), pp.group.expMat pp.generator (Aᵀ * V)⟩,
        ⟨A, W, U, V, c, w, v, (basisMatrix G κ pp A c)⁻¹⟩) := rfl

/-- On a singular setup the simulator explicitly uses a zero inverse basis. This totalizes
[Wee20, §4.2, p. 10, Setup*] without resampling or altering its unconditioned draws.

**Proof sketch.** Read `simSetupCore_eq` and apply `Matrix.nonsing_inv_apply_not_isUnit`. -/
theorem simSetupCore_singular (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (ω : SimSetupDraw G ℓ zDim κ pp)
    (h : ¬ IsUnit (basisMatrix G κ pp ω.1 ω.2.1).det) :
    (simSetupCore G ℓ zDim κ pp ω).2.basisInv = 0 := by
  rw [simSetupCore_eq]
  exact Matrix.nonsing_inv_apply_not_isUnit _ h

/-- Simulated encryption reveals only the three preselected group masks
[Wee20, §4.2, p. 10, Enc*]. The public input is accepted but does not affect these masks. -/
def simEncCore (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (_x : Fin (ℓ.eval κ) → ZMod pp.group.order) :
    CT G zDim κ pp :=
  ⟨pp.group.expVec pp.generator st.c, pp.group.expVec pp.generator st.w,
    pp.group.expVec pp.generator st.v⟩

/-- The ideal ciphertext is the three implicit masks retained in simulator state. -/
theorem simEncCore_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (st : SimState G ℓ zDim κ pp)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) :
    simEncCore G ℓ zDim κ pp st x =
      ⟨pp.group.expVec pp.generator st.c, pp.group.expVec pp.generator st.w,
        pp.group.expVec pp.generator st.v⟩ := rfl

/-- Combine two projected group rows and one hidden row by a known inverse basis
[Wee20, §4.2, p. 10, (12)]. This uses known scalar powers only. -/
def combineRows (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) {J : Type}
    (C : Matrix (Fin 3) (Fin 2) (ZMod pp.group.order)) (a : Fin 3 → ZMod pp.group.order)
    (hi : Matrix (Fin 2) J pp.group.G) (lo : J → pp.group.G) : Matrix (Fin 3) J pp.group.G :=
  matMulGroup C hi ⊙ (fun i j => lo j ^ (a i).val)

/-- The inverse-basis combination is its known-matrix action times the hidden-row powers. -/
theorem combineRows_eq (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) {J : Type}
    (C : Matrix (Fin 3) (Fin 2) (ZMod pp.group.order)) (a : Fin 3 → ZMod pp.group.order)
    (hi : Matrix (Fin 2) J pp.group.G) (lo : J → pp.group.G) :
    combineRows G κ pp C a hi lo = matMulGroup C hi ⊙ (fun i j => lo j ^ (a i).val) := rfl

/-- A simulated key draws `T`, the independent `uhat`, `R`, and partial-garbling coins
[Wee20, §4.2, p. 10, KeyGen* and (12)]. -/
abbrev SimKeyDraw (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) :=
  Matrix (Fin 3) (PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ)) (ZMod pp.group.order) ×
    ((Fin (ℓ.eval κ) × PG.MIdx κ pp.orderParam f) → ZMod pp.group.order) ×
    Matrix (Fin 2) (PG.MIdx κ pp.orderParam f) (ZMod pp.group.order) ×
    ((PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ)) → ZMod pp.group.order)

/-- Simulated-key randomness has exactly its four scalar blocks. -/
theorem simKeyDraw_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) :
    SimKeyDraw G PG κ pp f =
      (Matrix (Fin 3) (PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ))
          (ZMod pp.group.order) ×
        ((Fin (ℓ.eval κ) × PG.MIdx κ pp.orderParam f) → ZMod pp.group.order) ×
        Matrix (Fin 2) (PG.MIdx κ pp.orderParam f) (ZMod pp.group.order) ×
        ((PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ)) → ZMod pp.group.order)) := rfl

instance instSimKeyDrawFinite (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) :
    Fintype (SimKeyDraw G PG κ pp f) := inferInstance

instance instSimKeyDrawNonempty (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) :
    Nonempty (SimKeyDraw G PG κ pp f) := inferInstance

/-- Simulated key generation computes equation (12) from the group-valued allowed value
[Wee20, §4.2, p. 10]. The rectangular key matrix is used through group actions only. -/
def simKeyCore (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (f : Fn κ pp.orderParam)
    (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (mu : pp.group.G)
    (ω : SimKeyDraw G PG κ pp f) : Key G PG κ pp f :=
  let T := ω.1
  let uhat := ω.2.1
  let R := ω.2.2.1
  let t := ω.2.2.2
  let A := st.Aᵀ
  let tensorR := Matrix.kroneckerMap (fun a b => a * b)
    (1 : Matrix (Fin (ℓ.eval κ)) (Fin (ℓ.eval κ)) (ZMod pp.group.order)) R
  let X := PartialGarbling.publicTensor (p := pp.orderParam)
    (M := PG.MIdx κ pp.orderParam f) x
  let pstar := groupPGStar G PG κ pp f x mu t
  let high1 := pp.group.expMat pp.generator (A * (show Matrix (Fin 3) (Fin (n'.eval κ)) (ZMod
    pp.group.order) from
      fun i j => T i (Sum.inr j))) ⊙
    matMulGroup (A * st.W) M
  let high2 := pp.group.expMat pp.generator
    ((A * T) * (show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f) + (A * st.U) *
      tensorR)
  let high3 := pp.group.expMat pp.generator
    ((A * T) * (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ pp.orderParam f) + (A * st.V) *
      R)
  let low1 := fun j => (pstar (Sum.inl j))⁻¹ * groupVecMul st.w M j
  let low2 := pp.group.expVec pp.generator uhat
  let low3 := fun u => pstar (Sum.inr u) *
    pp.group.expVec pp.generator (Matrix.vecMul st.v R - Matrix.vecMul uhat X) u
  let C := fun i j => st.basisInv i (Fin.castSucc j)
  let a := fun i => st.basisInv i (Fin.last 2)
  ⟨combineRows G κ pp C a high1 low1, combineRows G κ pp C a high2 low2,
    combineRows G κ pp C a high3 low3, pp.group.expMat pp.generator R⟩

/-- The simulated key's three blocks have the projected and hidden-row form of (12).

**Proof sketch.** The deterministic core and this equation use the same named blocks,
so the equation follows by reduction of the core alone. -/
theorem simKeyCore_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (f : Fn κ pp.orderParam)
    (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (mu : pp.group.G)
    (ω : SimKeyDraw G PG κ pp f) :
    simKeyCore G PG zDim κ pp st f M x mu ω =
      let T := ω.1
      let uhat := ω.2.1
      let R := ω.2.2.1
      let t := ω.2.2.2
      let A := st.Aᵀ
      let tensorR := Matrix.kroneckerMap (fun a b => a * b)
        (1 : Matrix (Fin (ℓ.eval κ)) (Fin (ℓ.eval κ)) (ZMod pp.group.order)) R
      let X := PartialGarbling.publicTensor (p := pp.orderParam)
        (M := PG.MIdx κ pp.orderParam f) x
      let pstar := groupPGStar G PG κ pp f x mu t
      let high1 := pp.group.expMat pp.generator (A * (show Matrix (Fin 3) (Fin (n'.eval κ)) (ZMod
        pp.group.order) from
      fun i j => T i (Sum.inr j))) ⊙
        matMulGroup (A * st.W) M
      let high2 := pp.group.expMat pp.generator
        ((A * T) * (show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f) + (A * st.U)
          * tensorR)
      let high3 := pp.group.expMat pp.generator
        ((A * T) * (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ pp.orderParam f) + (A * st.V)
          * R)
      let low1 := fun j => (pstar (Sum.inl j))⁻¹ * groupVecMul st.w M j
      let low2 := pp.group.expVec pp.generator uhat
      let low3 := fun u => pstar (Sum.inr u) *
        pp.group.expVec pp.generator (Matrix.vecMul st.v R - Matrix.vecMul uhat X) u
      let C := fun i j => st.basisInv i (Fin.castSucc j)
      let a := fun i => st.basisInv i (Fin.last 2)
      ⟨combineRows G κ pp C a high1 low1, combineRows G κ pp C a high2 low2,
        combineRows G κ pp C a high3 low3, pp.group.expMat pp.generator R⟩ := rfl

/-- The simulator's exact setup law uses one uniform draw and the displayed total core
[Wee20, §4.2, p. 10]. -/
noncomputable def simSetup (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) : ProbComp (MPK G ℓ zDim κ pp × SimState G ℓ zDim κ pp) :=
  (simSetupCore G ℓ zDim κ pp <$> (ProbComp.sample (SimSetupDraw G ℓ zDim κ pp)))

/-- Simulated setup has the displayed core-plus-draw law. -/
theorem simSetup_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    simSetup G ℓ zDim κ pp =
      (simSetupCore G ℓ zDim κ pp <$> (ProbComp.sample (SimSetupDraw G ℓ zDim κ pp))) := rfl

/-- Simulated encryption is deterministic after setup chooses its masks
[Wee20, §4.2, p. 10, Enc*]. -/
def simEnc (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (x : Fin (ℓ.eval κ) → ZMod pp.group.order) :
    ProbComp (CT G zDim κ pp) := .pure (simEncCore G ℓ zDim κ pp st x)

/-- Simulated encryption returns its deterministic core output. -/
theorem simEnc_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (x : Fin (ℓ.eval κ) → ZMod pp.group.order) :
    simEnc G ℓ zDim κ pp st x = .pure (simEncCore G ℓ zDim κ pp st x) := rfl

/-- Simulated key generation samples its one function-dependent draw and runs equation (12)
[Wee20, §4.2, p. 10]. -/
noncomputable def simKey (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (f : Fn κ pp.orderParam)
    (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (mu : pp.group.G) :
    ProbComp (Key G PG κ pp f) :=
  (simKeyCore G PG zDim κ pp st f M x mu <$> (ProbComp.sample (SimKeyDraw G PG κ pp f)))

/-- Simulated keys have the displayed core-plus-draw law. -/
theorem simKey_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (f : Fn κ pp.orderParam)
    (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (mu : pp.group.G) :
    simKey G PG zDim κ pp st f M x mu =
      (simKeyCore G PG zDim κ pp st f M x mu <$> (ProbComp.sample (SimKeyDraw G PG κ pp f))) :=
  rfl

/-- The exact failure probability of an unconditioned uniform three-by-three basis is
one minus its general-linear-group fraction. This replaces the printed `1/p` bound in
[Wee20, §4.2, p. 10, Setup*] for its actual unconditioned draws. -/
noncomputable def rankSlack {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) : ℝ :=
  1 - (1 - 1 / (pp.group.order : ℝ)) *
    (1 - 1 / (pp.group.order : ℝ) ^ 2) * (1 - 1 / (pp.group.order : ℝ) ^ 3)

/-- The exact rank correction is the displayed three-by-three singular fraction. -/
theorem rankSlack_eq {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) :
    rankSlack pp = 1 - (1 - 1 / (pp.group.order : ℝ)) *
      (1 - 1 / (pp.group.order : ℝ) ^ 2) * (1 - 1 / (pp.group.order : ℝ) ^ 3) := rfl

/-- The good basis event has exactly the general-linear-group fraction, with no conditioning
on the first two columns [Wee20, §4.2, p. 10, Setup*, exact reading of its draw].

**Proof sketch.** Reindex the independent `A,c` coordinates as a uniform three-by-three
matrix. Integrate unused masks. Count invertible matrices with `Matrix.card_GL_field` and
divide by the cardinality of all matrices, using `ZMod.card`. -/
theorem simSetup_fullRank_prob (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) :
    ProbComp.prob (ProbComp.sample (SimSetupDraw G ℓ zDim κ pp))
      (fun ω => IsUnit (basisMatrix G κ pp ω.1 ω.2.1).det) = 1 - rankSlack pp := by
  classical
  let K := ZMod pp.group.order
  let Tail : Type :=
    Matrix (Fin 3) (Fin (zDim.eval κ)) K ×
      Matrix (Fin 3) (Fin (ℓ.eval κ) × Fin 2) K ×
      Matrix (Fin 3) (Fin 2) K ×
      (Fin (zDim.eval κ) → K) × (Fin 2 → K)
  let row : ((Fin 2 → K) × K) ≃ (Fin 3 → K) :=
    (Equiv.prodComm (Fin 2 → K) K).trans
      (Fin.snocEquiv (fun _ : Fin 3 => K))
  let ac : (Matrix (Fin 3) (Fin 2) K × (Fin 3 → K)) ≃
      Matrix (Fin 3) (Fin 3) K :=
    (Equiv.arrowProdEquivProdArrow (Fin 3)
      (fun _ => Fin 2 → K) (fun _ => K)).symm.trans
      ((Equiv.piCongrRight (fun _ : Fin 3 => row)).trans
        (Equiv.piComm (fun (_ : Fin 3) (_ : Fin 3) => K)))
  let e : SimSetupDraw G ℓ zDim κ pp ≃ (Matrix (Fin 3) (Fin 3) K × Tail) :=
    (Equiv.prodAssoc (Matrix (Fin 3) (Fin 2) K) (Fin 3 → K) Tail).symm.trans
      (Equiv.prodCongr ac (Equiv.refl Tail))
  have hBasis : ∀ ω : SimSetupDraw G ℓ zDim κ pp,
      (e ω).1 = basisMatrix G κ pp ω.1 ω.2.1 := by
    intro ω
    exact (basisMatrix_eq G κ pp ω.1 ω.2.1).symm
  have hEvent :
      (fun ω : SimSetupDraw G ℓ zDim κ pp =>
        IsUnit (basisMatrix G κ pp ω.1 ω.2.1).det) =
      (fun ω : SimSetupDraw G ℓ zDim κ pp => IsUnit (e ω).1) := ?_
  swap
  · funext ω
    rw [hBasis ω]
    exact propext (Matrix.isUnit_iff_isUnit_det _).symm
  have hDist :
      ProbComp.prob (ProbComp.sample (SimSetupDraw G ℓ zDim κ pp))
          (fun ω => IsUnit (basisMatrix G κ pp ω.1 ω.2.1).det) =
        ProbComp.prob (ProbComp.sample (Matrix (Fin 3) (Fin 3) K))
          (fun M => IsUnit M) := ?_
  swap
  · rw [Bridge.prob_sample_eq_uprob, Bridge.prob_sample_eq_uprob, hEvent]
    exact (uprob_comp_equiv e
      (fun z : Matrix (Fin 3) (Fin 3) K × Tail => IsUnit z.1)).trans
        (uprob_fst (β := Tail) (fun M : Matrix (Fin 3) (Fin 3) K => IsUnit M))
  have hCount :
      (((∏ i : Fin 3,
          (Fintype.card K ^ 3 - Fintype.card K ^ (i : ℕ))) : ℕ) : ℝ) /
          (Fintype.card K : ℝ) ^ (3 * 3) =
        (1 - 1 / (pp.group.order : ℝ)) *
          (1 - 1 / (pp.group.order : ℝ) ^ 2) *
          (1 - 1 / (pp.group.order : ℝ) ^ 3) := by
    let q : ℕ := pp.group.order
    have hq₂ : 2 ≤ q := pp.group.order_prime.two_le
    have hq₁ : 1 ≤ q := (Nat.le_add_right 1 1).trans hq₂
    have h31 : 1 ≤ q ^ 3 := one_le_pow₀ hq₁
    have h3q : q ≤ q ^ 3 := le_self_pow₀ hq₁ (Nat.succ_ne_zero 2)
    have h32 : q ^ 2 ≤ q ^ 3 := pow_le_pow_right₀ hq₁ (Nat.le_succ 2)
    have hqne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr pp.group.order_prime.ne_zero
    have hcard : Fintype.card K = q := ZMod.card pp.group.order
    rw [hcard, Fin.prod_univ_three]
    change (((q ^ 3 - q ^ 0) * (q ^ 3 - q ^ 1) * (q ^ 3 - q ^ 2) : ℕ) : ℝ) /
        (q : ℝ) ^ 9 =
      (1 - 1 / (q : ℝ)) * (1 - 1 / (q : ℝ) ^ 2) *
        (1 - 1 / (q : ℝ) ^ 3)
    simp only [pow_zero, pow_one, Nat.cast_mul, Nat.cast_sub h31,
      Nat.cast_sub h3q, Nat.cast_sub h32, Nat.cast_pow, Nat.cast_one]
    field_simp [hqne] <;> ring
  calc
    _ = ProbComp.prob (ProbComp.sample (Matrix (Fin 3) (Fin 3) K))
        (fun M => IsUnit M) := hDist
    _ = _ := prob_sample_matrix_isUnit_eq (K := K) 3
    _ = _ := hCount
    _ = 1 - rankSlack pp := ?_
  rw [rankSlack_eq]
  ring

/-- Π's statistical correction averages its exact rank failure over sequential public-
parameter generation [Wee20, Appendix B, Theorem 1, p. 12, with exact rank accounting]. -/
noncomputable def linearSlack (G : BilinearGen) (κ : ℕ) : ℝ :=
  ProbComp.expect (publicParamsGen G κ) rankSlack

/-- The linear-layer correction is the expectation of its exact rank failure. -/
theorem linearSlack_eq (G : BilinearGen) (κ : ℕ) :
    linearSlack G κ = ProbComp.expect (publicParamsGen G κ) rankSlack := rfl

/-- The two public projection rows and the final hidden row reconstruct an arbitrary
source-group matrix when their known coefficient matrix is a left inverse of the
augmented basis [Wee20, §4.2, p. 10, (12); Appendix B, Game 2, p. 13]. This is technical
group-arithmetic glue; all group entries remain arbitrary.

**Proof sketch.** Join the two-plus-one products with Fin.prod_univ_castSucc and the
published combineRows/basisMatrix readers. Consume groupVecMul_matMulGroup whole for
each row, read the scalar matrix product, and apply the supplied left-inverse identity.
Existing product-single and scalar identity-coordinate laws give the reconstructed row. -/
theorem combineRows_reconstruct (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) {J : Type}
    (A : Matrix (Fin 3) (Fin 2) (ZMod pp.group.order)) (c : Fin 3 → ZMod pp.group.order)
    (Q : Matrix (Fin 3) (Fin 3) (ZMod pp.group.order)) (K : Matrix (Fin 3) J pp.group.G)
    (hQ : Q * basisMatrix G κ pp A c = 1) :
    combineRows G κ pp (fun i j => Q i (Fin.castSucc j)) (fun i => Q i (Fin.last 2))
      (matMulGroup Aᵀ K) (groupVecMul c K) = K := by
  classical
  let H := basisMatrix G κ pp A c
  have hJoin :
      combineRows G κ pp (fun i j => Q i (Fin.castSucc j)) (fun i => Q i (Fin.last 2))
        (matMulGroup Aᵀ K) (groupVecMul c K) = matMulGroup Q (matMulGroup H K) := ?_
  swap
  · funext i j
    simp only [combineRows_eq, Matrix.hadamard_apply, matMulGroup_apply,
      groupVecMul_apply, groupDot_eq]
    rw [Fin.prod_univ_castSucc (fun u : Fin 3 =>
      (∏ k : Fin 3, K k j ^ (H u k).val) ^ (Q i u).val)]
    simp only [H, basisMatrix_eq, Fin.snoc_castSucc, Fin.snoc_last, Matrix.transpose_apply]
  rw [hJoin]
  funext i j
  change groupVecMul (Q i) (matMulGroup H K) j = K i j
  rw [pp.group.groupVecMul_matMulGroup (Q i) H K]
  have hScalar : Matrix.vecMul (Q i) H = (1 : Matrix (Fin 3) (Fin 3)
      (ZMod pp.group.order)) i :=
    (Matrix.mul_apply_eq_vecMul Q H i).symm.trans (congrFun hQ i)
  rw [hScalar]
  have hOne : (1 : ZMod pp.group.order).val = 1 :=
    ZMod.val_one'' pp.group.order_prime.ne_one
  simpa only [groupVecMul_apply, groupDot_eq, Matrix.one_apply, apply_ite,
    hOne, ZMod.val_zero, pow_one, pow_zero] using
      (Fintype.prod_ite_eq i (fun k : Fin 3 => K k j))

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
