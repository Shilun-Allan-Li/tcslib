/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Data

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Explicit ciphertext and key formulas for the linear hybrids

## Main definitions

* `Wee20.Linear.maskedCipher`: the real mask formula at any group-valued first block.
* `Wee20.Linear.decomposedKey`: the inverse-basis form of the actual honest key.
* `Wee20.Linear.ProjectedKey`, `projectedKey`: public projected key rows from group `R`.
* `Wee20.Linear.semiKey`: the two middle hybrid key formulas, from group `R` and `uhat`.

## Main results

Every formula has a proved equation reader. All operations on unknown group elements are
products or powers by known scalar coefficients. No draw, machine or decoder is constructed.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Appendix B, pp. 12–14,
  Games 1–4; §4.2, p. 10, (12).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

open Complexity TCSlib.Cryptography.Pairing
open scoped Matrix

/-- Form the masked ciphertext at any supplied GROUP first block
[Wee20, Appendix B, p. 12, Game 1]. -/
def maskedCipher (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : MSK G ℓ zDim κ pp) (c : Fin 3 → pp.group.G)
    (msg : Challenge G ℓ zDim κ pp) : CT G zDim κ pp :=
  ⟨c, pp.group.expVec pp.generator msg.2 * groupMatMul (fun _ : Fin 1 => c) st.W 0,
    groupMatMul (fun _ : Fin 1 => c)
      (st.U * (show Matrix _ _ (ZMod pp.group.order) from PartialGarbling.publicTensor (p :=
        pp.orderParam) (M := Fin 2) msg.1) + st.V) 0⟩

/-- The masked ciphertext is its displayed group row action and known-input mask. -/
theorem maskedCipher_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (st : MSK G ℓ zDim κ pp) (c : Fin 3 → pp.group.G)
    (msg : Challenge G ℓ zDim κ pp) :
    maskedCipher G ℓ zDim κ pp st c msg =
      ⟨c, pp.group.expVec pp.generator msg.2 * groupMatMul (fun _ : Fin 1 => c) st.W 0,
        groupMatMul (fun _ : Fin 1 => c)
          (st.U * (show Matrix _ _ (ZMod pp.group.order) from PartialGarbling.publicTensor (p :=
            pp.orderParam) (M := Fin 2) msg.1) + st.V)
          0⟩ := rfl

/-- Rewrite the actual honest key through the known projected and hidden basis rows
[Wee20, Appendix B, p. 13, Game 2]. The total inverse is used even on singular inputs. -/
def decomposedKey (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (query : KeyQuery G PG zDim κ pp)
    (ω : KeyDraw G PG κ pp query.fn) : Key G PG κ pp query.fn :=
  let sk := keyCore G PG zDim κ pp ⟨st.W, st.U, st.V⟩ query.fn query.matrix ω
  let C := fun i j => st.basisInv i (Fin.castSucc j)
  let a := fun i => st.basisInv i (Fin.last 2)
  ⟨combineRows G κ pp C a (matMulGroup st.Aᵀ sk.K1) (groupVecMul st.c sk.K1),
    combineRows G κ pp C a (matMulGroup st.Aᵀ sk.K2) (groupVecMul st.c sk.K2),
    combineRows G κ pp C a (matMulGroup st.Aᵀ sk.K3) (groupVecMul st.c sk.K3), sk.R⟩

/-- The second-game key has the exact projected/hidden decomposition of the honest key. -/
theorem decomposedKey_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (query : KeyQuery G PG zDim κ pp)
    (ω : KeyDraw G PG κ pp query.fn) :
    decomposedKey G PG zDim κ pp st query ω =
      let sk := keyCore G PG zDim κ pp ⟨st.W, st.U, st.V⟩ query.fn query.matrix ω
      let C := fun i j => st.basisInv i (Fin.castSucc j)
      let a := fun i => st.basisInv i (Fin.last 2)
      ⟨combineRows G κ pp C a (matMulGroup st.Aᵀ sk.K1) (groupVecMul st.c sk.K1),
        combineRows G κ pp C a (matMulGroup st.Aᵀ sk.K2) (groupVecMul st.c sk.K2),
        combineRows G κ pp C a (matMulGroup st.Aᵀ sk.K3) (groupVecMul st.c sk.K3), sk.R⟩ := rfl

/-- The public projected part of a key consists of its three two-row blocks
[Wee20, Appendix B, p. 13, Game 2]. -/
structure ProjectedKey (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) where
  /-- The output block. -/
  K1 : Matrix (Fin 2) (Fin (n'.eval κ)) pp.group.G
  /-- The public-variable block. -/
  K2 : Matrix (Fin 2) (Fin (ℓ.eval κ) × PG.MIdx κ pp.orderParam f) pp.group.G
  /-- The constant block. -/
  K3 : Matrix (Fin 2) (PG.MIdx κ pp.orderParam f) pp.group.G

/-- Compute the projected rows from known T and GROUP R
[Wee20, Appendix B, p. 13, Games 3–4]. This form is usable by the MDDH reduction. -/
def projectedKey (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (query : KeyQuery G PG zDim κ pp)
    (T : Matrix (Fin 3) (PG.TIdx κ pp.orderParam query.fn ⊕ Fin (n'.eval κ))
      (ZMod pp.group.order))
    (R : Matrix (Fin 2) (PG.MIdx κ pp.orderParam query.fn) pp.group.G) :
    ProjectedKey G PG κ pp query.fn :=
  let A := st.Aᵀ
  let tensorR := Matrix.kroneckerMap (fun a b => b ^ a.val)
    (1 : Matrix (Fin (ℓ.eval κ)) (Fin (ℓ.eval κ)) (ZMod pp.group.order)) R
  ⟨pp.group.expMat pp.generator (A * (show Matrix (Fin 3) (Fin (n'.eval κ)) (ZMod pp.group.order)
    from
      fun i j => T i (Sum.inr j))) ⊙
      matMulGroup (A * st.W) query.matrix,
    pp.group.expMat pp.generator ((A * T) * (show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ
      pp.orderParam query.fn)) ⊙
      matMulGroup (A * st.U) tensorR,
    pp.group.expMat pp.generator ((A * T) * (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ
      pp.orderParam query.fn)) ⊙
      matMulGroup (A * st.V) R⟩

/-- Projected key rows use known scalar coefficients and the supplied group matrix R. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem projectedKey_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (query : KeyQuery G PG zDim κ pp)
    (T : Matrix (Fin 3) (PG.TIdx κ pp.orderParam query.fn ⊕ Fin (n'.eval κ))
      (ZMod pp.group.order))
    (R : Matrix (Fin 2) (PG.MIdx κ pp.orderParam query.fn) pp.group.G) :
    projectedKey G PG zDim κ pp st query T R =
      let A := st.Aᵀ
      let tensorR := Matrix.kroneckerMap (fun a b => b ^ a.val)
        (1 : Matrix (Fin (ℓ.eval κ)) (Fin (ℓ.eval κ)) (ZMod pp.group.order)) R
      ⟨pp.group.expMat pp.generator (A * (show Matrix (Fin 3) (Fin (n'.eval κ)) (ZMod
        pp.group.order) from
      fun i j => T i (Sum.inr j))) ⊙
          matMulGroup (A * st.W) query.matrix,
        pp.group.expMat pp.generator ((A * T) * (show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ
          pp.orderParam query.fn)) ⊙
          matMulGroup (A * st.U) tensorR,
        pp.group.expMat pp.generator ((A * T) * (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ
          pp.orderParam query.fn)) ⊙
          matMulGroup (A * st.V) R⟩ := rfl

/-- The middle key formula accepts GROUP R and GROUP uhat, allowing the two MDDH challenge
branches to answer the same adaptive queries [Wee20, Appendix B, p. 13, Games 3–4]. -/
def semiKey (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (msg : Challenge G ℓ zDim κ pp)
    (query : KeyQuery G PG zDim κ pp)
    (T : Matrix (Fin 3) (PG.TIdx κ pp.orderParam query.fn ⊕ Fin (n'.eval κ))
      (ZMod pp.group.order))
    (t : (PG.TIdx κ pp.orderParam query.fn ⊕ Fin (n'.eval κ)) → ZMod pp.group.order)
    (R : Matrix (Fin 2) (PG.MIdx κ pp.orderParam query.fn) pp.group.G)
    (uhat : (Fin (ℓ.eval κ) × PG.MIdx κ pp.orderParam query.fn) → pp.group.G) :
    Key G PG κ pp query.fn :=
  let high := projectedKey G PG zDim κ pp st query T R
  let X := PartialGarbling.publicTensor (p := pp.orderParam)
    (M := PG.MIdx κ pp.orderParam query.fn) msg.1
  let low1 := pp.group.expVec pp.generator (fun j => t (Sum.inr j)) *
    groupVecMul (st.w - msg.2) query.matrix
  let low2 := pp.group.expVec pp.generator (Matrix.vecMul t ((show Matrix _ _ (ZMod pp.group.order)
    from PG.L1 κ pp.orderParam query.fn))) *
    uhat
  let low3 := fun u => pp.generator ^ (Matrix.vecMul t ((show Matrix _ _ (ZMod pp.group.order) from
    PG.L0 κ pp.orderParam query.fn)) u).val *
    (groupDot uhat (fun i => X i u))⁻¹ * groupVecMul st.v R u
  let C := fun i j => st.basisInv i (Fin.castSucc j)
  let a := fun i => st.basisInv i (Fin.last 2)
  ⟨combineRows G κ pp C a high.K1 low1, combineRows G κ pp C a high.K2 low2,
    combineRows G κ pp C a high.K3 low3, R⟩

/-- The middle key is its exact projected part and displayed hidden-row formulas. 

**Proof sketch.** The equation displays the same branch formulas and named blocks as the
deterministic definition, so reducing that definition alone gives the stated equation. -/
theorem semiKey_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ zDim κ pp) (msg : Challenge G ℓ zDim κ pp)
    (query : KeyQuery G PG zDim κ pp)
    (T : Matrix (Fin 3) (PG.TIdx κ pp.orderParam query.fn ⊕ Fin (n'.eval κ))
      (ZMod pp.group.order))
    (t : (PG.TIdx κ pp.orderParam query.fn ⊕ Fin (n'.eval κ)) → ZMod pp.group.order)
    (R : Matrix (Fin 2) (PG.MIdx κ pp.orderParam query.fn) pp.group.G)
    (uhat : (Fin (ℓ.eval κ) × PG.MIdx κ pp.orderParam query.fn) → pp.group.G) :
    semiKey G PG zDim κ pp st msg query T t R uhat =
      let high := projectedKey G PG zDim κ pp st query T R
      let X := PartialGarbling.publicTensor (p := pp.orderParam)
        (M := PG.MIdx κ pp.orderParam query.fn) msg.1
      let low1 := pp.group.expVec pp.generator (fun j => t (Sum.inr j)) *
        groupVecMul (st.w - msg.2) query.matrix
      let low2 :=
        pp.group.expVec pp.generator (Matrix.vecMul t ((show Matrix _ _ (ZMod pp.group.order) from
          PG.L1 κ pp.orderParam query.fn))) * uhat
      let low3 := fun u =>
        pp.generator ^ (Matrix.vecMul t ((show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ
          pp.orderParam query.fn)) u).val *
          (groupDot uhat (fun i => X i u))⁻¹ * groupVecMul st.v R u
      let C := fun i j => st.basisInv i (Fin.castSucc j)
      let a := fun i => st.basisInv i (Fin.last 2)
      ⟨combineRows G κ pp C a high.K1 low1, combineRows G κ pp C a high.K2 low2,
        combineRows G κ pp C a high.K3 low3, R⟩ := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
