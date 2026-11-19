/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearCorrect

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Correctness of raw quadratic PHFE

The scalar masking matrices occur only as the known setup draw in the correctness theorem.
The honest encryption algorithm itself uses only the public group matrices. The proof
connects those group computations to the scalar tensor identities (4) and (5), then applies
Π's perfect correctness theorem.

## Main definitions

This module introduces no algorithms or alternative tensor representations.

## Main results

* `Wee20.Quadratic.mixGroup_exp`, `signalGroup_exp`: source-group algorithms agree with
  their scalar proof representations on known scalar inputs.
* `Wee20.Quadratic.cross_tensor_identity`: the two cross terms give equation (4).
* `Wee20.Quadratic.cross_value_identity`: scalar evaluation gives equation (5).
* `Wee20.Quadratic.quadratic_dec_eq`, `scheme_raw_correct`: perfect correctness in the
  target group for every honest draw.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §3.1, p. 6, (4)–(5),
  and §4.2, p. 10, (11).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic

open Complexity TCSlib.Cryptography.Pairing
open scoped Matrix

/-- The public group mixing matrix is the implicit representation of the two scalar
Kronecker blocks [Wee20, §3.1, p. 6, Setup].

**Proof sketch.** Read the two mixing-matrix readers and split the canonical sum
coordinate. The Kronecker entry reader and the modular multiplication and iterated-power
laws identify each entry. This covers the identity coefficients without extra cases. -/
theorem mixGroup_exp (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (A1 : Matrix (Fin 2) (Fin (n1.eval κ)) (ZMod pp.group.order))
    (A2 : Matrix (Fin 2) (Fin (n2.eval κ)) (ZMod pp.group.order)) :
    mixGroup G n1 n2 κ pp (pp.group.expMat pp.generator A1)
        (pp.group.expMat pp.generator A2) =
      pp.group.expMat pp.generator (mixScalar (p := pp.orderParam) A1 A2) := by
  funext i j
  simp only [mixGroup_eq, mixScalar_eq, BilinearGroup.expMat_apply]
  cases hi : (signalCoord (n1.eval κ) (n2.eval κ)).symm i with
  | inl u =>
      simp only [hi, Sum.elim_inl, Matrix.kroneckerMap_apply,
        BilinearGroup.expMat_apply, pp.group.pow_val_mul, pow_mul]
  | inr u =>
      simp only [hi, Sum.elim_inr, Matrix.kroneckerMap_apply,
        BilinearGroup.expMat_apply, pp.group.pow_val_mul, mul_comm, pow_mul]

/-- When its group input is a known scalar vector, the encryption signal is exactly the
implicit scalar cross-term signal [Wee20, §3.1, p. 6, Enc].

**Proof sketch.** Read the canonical sum/product coordinates. The first block is already
the implicit private tensor. For the second block use `expVec_tensor_left` and the existing
private-tensor reader; no scalar is recovered from the group input. -/
theorem signalGroup_exp (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (s1 s2 : Fin 2 → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order)
    (y1 : Fin (n1.eval κ) → ZMod pp.group.order) :
    signalGroup G n1 n2 κ pp s1 z2 (pp.group.expVec pp.generator y1) s2 =
      pp.group.expVec pp.generator (signalScalar (p := pp.orderParam) s1 z2 y1 s2) := by
  funext i
  simp only [signalGroup_eq, signalScalar_eq, BilinearGroup.expVec_apply]
  cases hi : (signalCoord (n1.eval κ) (n2.eval κ)).symm i with
  | inl u => simp only [hi, Sum.elim_inl]
  | inr u =>
      simp only [hi, Sum.elim_inr, privateTensor_eq, Matrix.kroneckerMap_apply,
        Equiv.symm_apply_apply]
      simpa only [BilinearGroup.expVec_apply] using
        congrFun (pp.group.expVec_tensor_left pp.generator y1 s2) u

/-- The two cross terms account for the masked tensor product
[Wee20, §3.1, p. 6, (4)].

**Proof sketch.** Reindex by the canonical output pair. Apply the mixed-product property
to each Kronecker block. The two block contributions are `(s1 A1)⊗z2` and `y1⊗(s2 A2)`.
Expand `y1=s1 A1+z1` and `y2=s2 A2+z2`; distributivity gives the identity. -/
theorem cross_tensor_identity {p : ℕ+} {n1 n2 : ℕ}
    (A1 : Matrix (Fin 2) (Fin n1) (ZMod (p : ℕ)))
    (A2 : Matrix (Fin 2) (Fin n2) (ZMod (p : ℕ)))
    (s1 s2 : Fin 2 → ZMod (p : ℕ)) (z1 : Fin n1 → ZMod (p : ℕ))
    (z2 : Fin n2 → ZMod (p : ℕ)) :
    let y1 := Matrix.vecMul s1 A1 + z1
    let y2 := Matrix.vecMul s2 A2 + z2
    privateTensor (p := p) y1 y2 = privateTensor (p := p) z1 z2 +
      Matrix.vecMul (signalScalar (p := p) s1 z2 y1 s2) (mixScalar (p := p) A1 A2) := by
  let y1 := Matrix.vecMul s1 A1 + z1
  let y2 := Matrix.vecMul s2 A2 + z2
  let top := Matrix.kroneckerMap (fun a b => a * b) A1
    (1 : Matrix (Fin n2) (Fin n2) (ZMod (p : ℕ)))
  let bottom := Matrix.kroneckerMap (fun a b => a * b)
    (1 : Matrix (Fin n1) (Fin n1) (ZMod (p : ℕ))) A2
  change privateTensor (p := p) y1 y2 = privateTensor (p := p) z1 z2 +
    Matrix.vecMul (signalScalar (p := p) s1 z2 y1 s2) (mixScalar (p := p) A1 A2)
  funext q
  obtain ⟨⟨i, j⟩, rfl⟩ :=
    (finProdFinEquiv : Fin n1 × Fin n2 ≃ Fin (n1 * n2)).surjective q
  have hTop :
      dotProduct (fun u : Fin 2 × Fin n2 => s1 u.1 * z2 u.2)
        (fun u => top u (i, j)) = Matrix.vecMul s1 A1 i * z2 j := ?_
  swap
  · have h := congrFun (congrFun (Matrix.mul_kronecker_mul
        (fun (_ : Fin 1) k => s1 k) A1 (fun (_ : Fin 1) k => z2 k)
        (1 : Matrix (Fin n2) (Fin n2) (ZMod (p : ℕ)))) (0, 0)) (i, j)
    rw [Matrix.mul_one] at h
    simpa only [Matrix.kroneckerMap_apply, Matrix.mul_apply'] using h.symm
  have hBottom :
      dotProduct (fun u : Fin n1 × Fin 2 => y1 u.1 * s2 u.2)
        (fun u => bottom u (i, j)) = y1 i * Matrix.vecMul s2 A2 j := ?_
  swap
  · have h := congrFun (congrFun (Matrix.mul_kronecker_mul
        (fun (_ : Fin 1) k => y1 k)
        (1 : Matrix (Fin n1) (Fin n1) (ZMod (p : ℕ)))
        (fun (_ : Fin 1) k => s2 k) A2) (0, 0)) (i, j)
    rw [Matrix.mul_one] at h
    simpa only [Matrix.kroneckerMap_apply, Matrix.mul_apply'] using h.symm
  have hCross :
      Matrix.vecMul (signalScalar (p := p) s1 z2 y1 s2)
          (mixScalar (p := p) A1 A2) (finProdFinEquiv (i, j)) =
        dotProduct (fun u : Fin 2 × Fin n2 => s1 u.1 * z2 u.2)
            (fun u => top u (i, j)) +
          dotProduct (fun u : Fin n1 × Fin 2 => y1 u.1 * s2 u.2)
            (fun u => bottom u (i, j)) := ?_
  swap
  · change dotProduct (signalScalar (p := p) s1 z2 y1 s2)
        (fun k => mixScalar (p := p) A1 A2 k (finProdFinEquiv (i, j))) = _
    rw [← comp_equiv_dotProduct_comp_equiv _ _ (signalCoord n1 n2)]
    change dotProduct
      (fun u : (Fin 2 × Fin n2) ⊕ (Fin n1 × Fin 2) =>
        signalScalar (p := p) s1 z2 y1 s2 (signalCoord n1 n2 u))
      (fun u => mixScalar (p := p) A1 A2 (signalCoord n1 n2 u)
        (finProdFinEquiv (i, j))) = _
    simp only [signalScalar_eq, mixScalar_eq, Equiv.symm_apply_apply]
    change dotProduct
      (Sum.elim
        (fun u : Fin 2 × Fin n2 =>
          privateTensor (p := p) s1 z2 (finProdFinEquiv u))
        (fun u : Fin n1 × Fin 2 =>
          privateTensor (p := p) y1 s2 (finProdFinEquiv u)))
      (Sum.elim (fun u => top u (i, j)) (fun u => bottom u (i, j))) = _
    rw [sumElim_dotProduct_sumElim]
    congr 1
    · apply congrArg₂ dotProduct _ rfl
      funext u
      simp only [privateTensor_eq, Matrix.kroneckerMap_apply, Equiv.symm_apply_apply]
    · apply congrArg₂ dotProduct _ rfl
      funext u
      simp only [privateTensor_eq, Matrix.kroneckerMap_apply, Equiv.symm_apply_apply]
  simp only [privateTensor_eq, Matrix.kroneckerMap_apply, Equiv.symm_apply_apply,
    Pi.add_apply]
  rw [hCross, hTop, hBottom]
  change (Matrix.vecMul s1 A1 i + z1 i) * (Matrix.vecMul s2 A2 j + z2 j) =
    z1 i * z2 j + (Matrix.vecMul s1 A1 i * z2 j +
      (Matrix.vecMul s1 A1 i + z1 i) * Matrix.vecMul s2 A2 j)
  ring

/-- Evaluating the cross-term identity isolates the desired private quadratic value
[Wee20, §3.1, p. 6, (5)].

**Proof sketch.** Take the scalar dot product of `cross_tensor_identity` with the supplied
function vector. Reuse dot-product linearity and matrix-action associativity, then rearrange. -/
theorem cross_value_identity {p : ℕ+} {n1 n2 : ℕ}
    (A1 : Matrix (Fin 2) (Fin n1) (ZMod (p : ℕ)))
    (A2 : Matrix (Fin 2) (Fin n2) (ZMod (p : ℕ)))
    (s1 s2 : Fin 2 → ZMod (p : ℕ)) (z1 : Fin n1 → ZMod (p : ℕ))
    (z2 : Fin n2 → ZMod (p : ℕ)) (fx : Fin (n1 * n2) → ZMod (p : ℕ)) :
    let y1 := Matrix.vecMul s1 A1 + z1
    let y2 := Matrix.vecMul s2 A2 + z2
    dotProduct (privateTensor (p := p) z1 z2) fx =
      dotProduct (privateTensor (p := p) y1 y2) fx -
        dotProduct (signalScalar (p := p) s1 z2 y1 s2)
          (mixScalar (p := p) A1 A2 *ᵥ fx) := by
  have h := congrArg (fun v : Fin (n1 * n2) → ZMod (p : ℕ) => dotProduct v fx)
    (cross_tensor_identity A1 A2 s1 s2 z1 z2)
  change dotProduct
      (privateTensor (p := p) (Matrix.vecMul s1 A1 + z1) (Matrix.vecMul s2 A2 + z2)) fx =
    dotProduct (privateTensor (p := p) z1 z2 +
      Matrix.vecMul (signalScalar (p := p) s1 z2 (Matrix.vecMul s1 A1 + z1) s2)
        (mixScalar (p := p) A1 A2)) fx at h
  rw [add_dotProduct, ← Matrix.dotProduct_mulVec] at h
  exact eq_sub_of_add_eq h.symm

/-- The raw quadratic scheme decrypts perfectly to the allowed value in the target group
for every honest setup, encryption and key draw [Wee20, §3.1, p. 6, (4)–(5)].

**Proof sketch.** Read the cores and use `expVec_vecMul` to identify the known scalar
masked vectors from the setup draw. Apply `mixGroup_exp` and `signalGroup_exp`, then Π's
`pi_dec_eq`. Use `cross_value_identity` to cancel Π's result from the paired tensor term.
Finish with the target-group additive and negation exponent laws. -/
theorem quadratic_dec_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ n1 n2 κ pp) (s : EncDraw G κ pp)
    (t : Linear.KeyDraw G PG κ pp f) :
    dec G n1 n2 PG κ pp f x
        (keyCore G n1 n2 PG κ pp (setupCore G ℓ n1 n2 κ pp a).2 f t)
        (encCore G ℓ n1 n2 κ pp (setupCore G ℓ n1 n2 κ pp a).1 x z1 z2 s) =
      pp.group.pair pp.generator pp.generator ^ (value G n1 n2 PG κ pp f x z1 z2).val := by
  let y1 := Matrix.vecMul s.1 a.1 + z1
  let y2 := Matrix.vecMul s.2.1 a.2.1 + z2
  let signal := signalScalar (p := pp.orderParam) s.1 z2 y1 s.2.1
  let F := mixScalar (p := pp.orderParam) a.1 a.2.1
  let fx := PG.eval κ pp.orderParam f x
  let egg := pp.group.pair pp.generator pp.generator
  have hTensor :
      (fun i => pp.group.pairTensor (pp.group.expVec pp.generator y1)
        (pp.group.expVec pp.generator y2) (finProdFinEquiv.symm i)) =
      pp.group.expVecT egg (privateTensor (p := pp.orderParam) y1 y2) := ?_
  swap
  · rw [pp.group.pairTensor_expVec]
    funext i
    simp only [pp.group.expVecT_apply, privateTensor_eq, Matrix.kroneckerMap_apply]
    rfl
  have hLeak :
      pp.group.pair pp.generator
          (Linear.leak G PG (piDim n1 n2) κ pp f
            (pp.group.expMat pp.generator F) x signal) =
        egg ^ (dotProduct signal (F *ᵥ fx)).val := ?_
  swap
  · rw [Linear.leak_eq, pp.group.expMat_mulVec, pp.group.groupDot_expVec,
      dotProduct_comm, pp.group.pair_pow_right]
  have hValue : dotProduct (privateTensor (p := pp.orderParam) z1 z2) fx =
      dotProduct (privateTensor (p := pp.orderParam) y1 y2) fx -
        dotProduct signal (F *ᵥ fx) :=
    cross_value_identity (p := pp.orderParam) a.1 a.2.1 s.1 s.2.1 z1 z2 fx
  simp only [dec_eq, keyCore_eq, encCore_eq, setupCore_eq,
    pp.group.expVec_vecMul, ← pp.group.expVec_add, mixGroup_exp, signalGroup_exp]
  rw [Linear.pi_dec_eq, hTensor, pp.group.groupDot_expVecT, hLeak, value_eq,
    hValue, sub_eq_add_neg, pp.group.pow_val_add_GT, pp.group.pow_val_neg_GT]

/-- The internal raw quadratic bundle inherits perfect correctness for every draw
[Wee20, §3.1, p. 6, (4)–(5)]. No efficiency target is assumed.

**Proof sketch.** Read `scheme_raw_eq` and apply `quadratic_dec_eq` to its four cores. -/
theorem scheme_raw_correct (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ n1 n2 κ pp) (s : EncDraw G κ pp)
    (t : Linear.KeyDraw G PG κ pp f) :
    let S := scheme_raw G n1 n2 PG κ pp
    S.dec f x (S.keyCore (S.setupCore a).2 f t)
        (S.encCore (S.setupCore a).1 x z1 z2 s) =
      pp.group.pair pp.generator pp.generator ^ (value G n1 n2 PG κ pp f x z1 z2).val := by
  rw [scheme_raw_eq]
  exact quadratic_dec_eq G n1 n2 PG κ pp f x z1 z2 a s t

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
