/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Correctness of the raw linear PHFE building block

The correctness statements allow arbitrary source-group key matrices. They do not choose
scalar witnesses for their entries. Instead, the partial-garbling reconstruction law is
specialized to scalar basis vectors, giving the coefficient identities needed to cancel
randomness in products of known powers.

## Main definitions

This module introduces no algorithms or new data representations.

## Main results

* `Wee20.Linear.rec_output_eq_eval`, `rec_matrix_eq`: coefficient consequences of the
  supplied raw partial-garbling reconstruction theorem.
* `Wee20.Linear.decFirst_correct`, `decSecond_correct`: equations (9) and (10), with a
  group-valued matrix and its known scalar inputs.
* `Wee20.Linear.pi_dec_eq`, `scheme_raw_correct`: perfect correctness in the target group,
  for every setup, encryption and key-generation draw.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §4.2, pp. 9–10, (6)–(11).
* [AGW20] M. Abdalla, J. Gong, and H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, CRYPTO 2020; full version, Cryptology ePrint Archive 2020/762,
  Lemma 2, p. 12, and Appendix A, (29)–(32), pp. 37–38.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

open Complexity TCSlib.Cryptography.Pairing
open scoped BigOperators Matrix

/-- The output part of reconstruction equals the function value. This is coefficient glue
from the reconstruction law [AGW20, Lemma 2, p. 12].

**Proof sketch.** Apply `PG.reconstruct` with zero draw and a single unit in the private
input. Use Mathlib's single-coordinate dot-product readers on both sides. -/
theorem rec_output_eq_eval (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (j : Fin (n'.eval κ)) :
    PG.recVec κ pp.orderParam f x (Sum.inl j) = PG.eval κ pp.orderParam f x j := by
  simpa only [PartialGarbling.Raw.pgb_eq, PartialGarbling.pgbCore_eq,
    Pi.zero_apply, sub_zero, Matrix.zero_vecMul, Sum.elim_single_zero,
    single_one_dotProduct] using
    (PG.reconstruct κ pp.orderParam f x (Pi.single j 1) 0)

/-- The reconstruction vector cancels every garbling-draw coordinate. This is coefficient
form of the reconstruction law [AGW20, Lemma 2, p. 12; Appendix A, (29), p. 37].

**Proof sketch.** Apply `PG.reconstruct` with zero private input and a single unit draw.
Use `rec_output_eq_eval` for its final draw block; move that term across the equality and
read the remaining coefficient through the single-coordinate dot-product lemmas. -/
theorem rec_matrix_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order) :
    ((show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f) *
        (show Matrix _ _ (ZMod pp.group.order) from PartialGarbling.publicTensor (p :=
          pp.orderParam) (M := PG.MIdx κ pp.orderParam f) x) +
      (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ pp.orderParam f)) *ᵥ (fun u => PG.recVec κ
        pp.orderParam f x (Sum.inr u)) =
        Sum.elim (fun _ => 0) (PG.eval κ pp.orderParam f x) := by
  funext i
  have h := PG.reconstruct κ pp.orderParam f x 0 (Pi.single i 1)
  rw [PartialGarbling.Raw.pgb_eq, PartialGarbling.pgbCore_eq,
    ← Sum.elim_comp_inl_inr (PG.recVec κ pp.orderParam f x),
    sumElim_dotProduct_sumElim, ← Matrix.dotProduct_mulVec, single_one_dotProduct,
    zero_dotProduct] at h
  cases i with
  | inl a =>
      simp only [Pi.zero_apply, Pi.single_eq_of_ne Sum.inr_ne_inl, sub_zero] at h
      change (0 : Fin (n'.eval κ) → ZMod pp.group.order) ⬝ᵥ _ + _ = _ at h
      simpa only [zero_dotProduct, zero_add, Sum.elim_inl] using h
  | inr j =>
      rw [← Sum.elim_zero_single j (1 : ZMod pp.group.order)] at h
      simp only [Sum.elim_inr, Pi.zero_apply, zero_sub] at h
      change (-Pi.single j (1 : ZMod pp.group.order)) ⬝ᵥ _ + _ = _ at h
      rw [neg_dotProduct, single_one_dotProduct] at h
      exact (eq_of_neg_add_eq_zero h).symm.trans (rec_output_eq_eval G PG κ pp f x j)

/-- The leakage is the product of the supplied group-matrix entries raised to the known
coefficients `z_a f_b(x)` [Wee20, §4, p. 8].

**Proof sketch.** Read `leak_eq`, `groupMulVec_apply` and `groupDot_eq`. Distribute powers
across finite products, use the source-group modular multiplication law, and commute the
two known scalar factors. No exponent of a group element is recovered. -/
theorem leak_product (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order) :
    leak G PG zDim κ pp f M x z =
      ∏ a, ∏ b, M a b ^ (z a * (show ZMod pp.group.order from PG.eval κ pp.orderParam f x b)).val :=
  by
    rw [leak_eq, groupDot_eq]
    apply Finset.prod_congr rfl
    intro a _
    rw [groupMulVec_apply, groupDot_eq, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro b _
    rw [← pow_mul, ← pp.group.pow_val_mul,
      mul_comm (PG.eval κ pp.orderParam f x b) (z a)]

/-- The first decryption block is the group-valued allowed input mask minus the last
coordinates of `sAT` [Wee20, §4.2, p. 10, (9)].

**Proof sketch.** Read the algorithm equations and transport the scalar actions with
`expVec_vecMul`. Apply pairing bilinearity and multiplicativity. The `sAWM` products cancel
entrywise, leaving the known-input action on the arbitrary group matrix and the `T` mask. -/
theorem decFirst_correct (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    decFirst G PG zDim κ pp f M
        (keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t)
        (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
          (pp.group.expVec pp.generator z) s) =
      fun j => pp.group.pair pp.generator (groupVecMul z M j) *
        (pp.group.pair pp.generator pp.generator) ^
          (-(Matrix.vecMul (Matrix.vecMul s a.1) t.1 (Sum.inr j))).val := by
  -- Normalize the ciphertext numerator while keeping M group-valued.
  have hCipher (j : Fin (n'.eval κ)) :
      pp.group.pairVec
          (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
            (pp.group.expVec pp.generator z) s).c1
          (fun k => M k j) =
        pp.group.pair pp.generator (groupVecMul z M j) *
          pp.group.pair pp.generator
            (groupVecMul (Matrix.vecMul (Matrix.vecMul s a.1) a.2.1) M j) := by
    simp only [encCore_eq, setupCore_eq]
    rw [pp.group.expVec_vecMul, ← pp.group.expVec_add,
      pp.group.pairVec_expVec_left]
    simp only [groupVecMul_apply, groupDot_eq, Pi.add_apply,
      pp.group.pow_val_add, Finset.prod_mul_distrib, map_mul,
      ← Matrix.vecMul_vecMul]
  -- The key pairing has the same mask and the known T-coordinate factor.
  have hKey (j : Fin (n'.eval κ)) :
      pp.group.pairVec
          (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
            (pp.group.expVec pp.generator z) s).c0
          (fun i => (keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t).K1 i j) =
        pp.group.pair pp.generator pp.generator ^
            (Matrix.vecMul (Matrix.vecMul s a.1) t.1 (Sum.inr j)).val *
          pp.group.pair pp.generator
            (groupVecMul (Matrix.vecMul (Matrix.vecMul s a.1) a.2.1) M j) := by
    have hT := pp.group.groupDot_expVec pp.generator
      (fun i => t.1 i (Sum.inr j)) (Matrix.vecMul s a.1)
    simp only [groupDot_eq, pp.group.expVec_apply] at hT
    rw [dotProduct_comm] at hT
    have hAssoc := congrFun
      (pp.group.groupVecMul_matMulGroup (Matrix.vecMul s a.1) a.2.1 M) j
    simp only [groupVecMul_apply, groupDot_eq] at hAssoc
    simp only [encCore_eq, setupCore_eq, keyCore_eq]
    rw [pp.group.expVec_vecMul, pp.group.pairVec_expVec_left]
    simp only [Matrix.hadamard_apply, pp.group.expMat_apply, groupDot_eq, mul_pow,
      Finset.prod_mul_distrib, map_mul, groupVecMul_apply]
    rw [hT, hAssoc, pp.group.pair_pow_right]
    rfl
  -- Cancel the shared mask using its target-group inverse.
  rw [decFirst_eq]
  funext j
  rw [hCipher j, hKey j, pp.group.pow_val_neg_GT, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel_right]

/-- The second decryption block is the second partial-garbling block at coins `sAT`
[Wee20, §4.2, p. 10, (10)].

**Proof sketch.** Use the known-scalar matrix and pairing transport laws. The mixed-product
identity `(I⊗R)(x⊗I)=(x⊗I)R` identifies the two `U` terms. Cancel them and the two `V`
terms; the remaining matrix expression is `(sAT)(L1(x⊗I)+L0)`. -/
theorem decSecond_correct (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    decSecond G PG zDim κ pp f x
        (keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t)
        (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
          (pp.group.expVec pp.generator z) s) =
      pp.group.expVecT (pp.group.pair pp.generator pp.generator)
        (Matrix.vecMul (Matrix.vecMul (Matrix.vecMul s a.1) t.1)
          ((show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f) *
              (show Matrix _ _ (ZMod pp.group.order) from PartialGarbling.publicTensor (p :=
                pp.orderParam)
                (M := PG.MIdx κ pp.orderParam f) x) + (show Matrix _ _ (ZMod pp.group.order) from
                  PG.L0 κ pp.orderParam f))) :=
  by
    let X := (show Matrix _ _ (ZMod pp.group.order) from
      PartialGarbling.publicTensor (p := pp.orderParam) (M := PG.MIdx κ pp.orderParam f) x)
    let X2 := (show Matrix _ _ (ZMod pp.group.order) from
      PartialGarbling.publicTensor (p := pp.orderParam) (M := Fin 2) x)
    let T := t.1
    let R := t.2
    let U := a.2.2.1
    let V := a.2.2.2
    let H := Matrix.kroneckerMap (fun c r => c * r)
      (1 : Matrix (Fin (ℓ.eval κ)) (Fin (ℓ.eval κ)) (ZMod pp.group.order)) R
    let L1m := (show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f)
    let L0m := (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ pp.orderParam f)
    let sa := Matrix.vecMul s a.1
    let value := Matrix.vecMul (Matrix.vecMul sa T) (L1m * X + L0m)
    let mask := Matrix.vecMul (Matrix.vecMul sa (U * X2 + V)) R
    let sk := keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t
    let ct := encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
      (pp.group.expVec pp.generator z) s
    let K := groupMatMul sk.K2 X
    have hMix : H * X = X2 * R := by
      exact PartialGarbling.kronecker_mul_publicTensor (p := pp.orderParam) x R
    have hMatrix : (T * L1m + U * H) * X + (T * L0m + V * R) =
        T * (L1m * X + L0m) + (U * X2 + V) * R := ?_
    swap
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hMix,
        add_assoc, add_comm, add_left_comm]
    have hNumerator (m : PG.MIdx κ pp.orderParam f) :
        pp.group.pairVec ct.c0 (fun i => K i m * sk.K3 i m) =
          pp.group.pair pp.generator pp.generator ^ (value m).val *
            pp.group.pair pp.generator pp.generator ^ (mask m).val := by
      have hColumn :
          (fun i => pp.group.expMat pp.generator ((T * L1m + U * H) * X) i m *
            pp.group.expMat pp.generator (T * L0m + V * R) i m) =
          pp.group.expVec pp.generator
            (fun i => (T * (L1m * X + L0m) + (U * X2 + V) * R) i m) := ?_
      swap
      · funext i
        rw [pp.group.expMat_apply, pp.group.expMat_apply, pp.group.expVec_apply,
          ← pp.group.pow_val_add]
        exact congrArg (fun c : ZMod pp.group.order => pp.generator ^ c.val)
          (congrFun (congrFun hMatrix i) m)
      dsimp only [ct, K, sk]
      simp only [encCore_eq, setupCore_eq, keyCore_eq]
      rw [pp.group.expVec_vecMul, pp.group.expMat_mul, hColumn,
        pp.group.pair_expVec]
      change pp.group.pair pp.generator pp.generator ^
        (Matrix.vecMul sa (T * (L1m * X + L0m) + (U * X2 + V) * R) m).val = _
      rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
      change pp.group.pair pp.generator pp.generator ^ (value m + mask m).val = _
      exact pp.group.pow_val_add_GT _ _ _
    have hDenominator (m : PG.MIdx κ pp.orderParam f) :
        pp.group.pairVec ct.c2 (fun i => sk.R i m) =
          pp.group.pair pp.generator pp.generator ^ (mask m).val := by
      have hR : (fun i => sk.R i m) =
          pp.group.expVec pp.generator (fun i => R i m) := ?_
      swap
      · funext i
        dsimp only [sk]
        simp only [keyCore_eq, pp.group.expMat_apply, pp.group.expVec_apply]
        rfl
      rw [hR]
      dsimp only [ct]
      simp only [encCore_eq, setupCore_eq]
      rw [pp.group.expMat_mul, pp.group.expVec_vecMul, pp.group.expVec_vecMul,
        ← pp.group.expVec_add, Matrix.mul_assoc, ← Matrix.vecMul_add,
        ← Matrix.mul_add, ← Matrix.vecMul_vecMul, pp.group.pair_expVec]
      rfl
    change decSecond G PG zDim κ pp f x sk ct =
      pp.group.expVecT (pp.group.pair pp.generator pp.generator) value
    rw [decSecond_eq]
    funext m
    rw [hNumerator m, hDenominator m, pp.group.expVecT_apply, mul_inv_cancel_right]

/-- Π decrypts to `e(g,[zMf(x)^T])` for every honest draw and an arbitrary source-group
matrix `M` [Wee20, §4.2, p. 10, (11)]. This is perfect correctness in the exponent.

**Proof sketch.** Substitute `decFirst_correct` and `decSecond_correct` into `dec_eq`.
Use the two reconstruction coefficient identities to cancel all `sAT` powers and identify
the remaining source-group product with `leak`. Multiplicativity of pairing gives the
claimed target-group value. This proof does not introduce scalar witnesses for `M`. -/
theorem pi_dec_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    dec G PG zDim κ pp f M x
        (keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t)
        (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
          (pp.group.expVec pp.generator z) s) =
      pp.group.pair pp.generator (leak G PG zDim κ pp f M x z) := by
  classical
  let v := Matrix.vecMul (Matrix.vecMul s a.1) t.1
  let K : Matrix (PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ))
      (PG.MIdx κ pp.orderParam f) (ZMod pp.group.order) :=
    (show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f) *
        (show Matrix _ _ (ZMod pp.group.order) from PartialGarbling.publicTensor
          (p := pp.orderParam) (M := PG.MIdx κ pp.orderParam f) x) +
      (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ pp.orderParam f)
  let e := PG.eval κ pp.orderParam f x
  let r := fun m => PG.recVec κ pp.orderParam f x (Sum.inr m)
  let egg := pp.group.pair pp.generator pp.generator
  have hRec : K *ᵥ r = Sum.elim (fun _ => 0) e := rec_matrix_eq G PG κ pp f x
  have hMask : dotProduct (Matrix.vecMul v K) r =
      dotProduct (fun j => v (Sum.inr j)) e := ?_
  swap
  · rw [← Matrix.dotProduct_mulVec, hRec, ← Sum.elim_comp_inl_inr v,
      sumElim_dotProduct_sumElim]
    simp only [dotProduct_zero', zero_add, Sum.elim_inr]
  have hLeak : groupDot (groupVecMul z M) e = leak G PG zDim κ pp f M x z := ?_
  swap
  · rw [groupDot_eq, leak_product]
    simp only [groupVecMul_apply, groupDot_eq, ← Finset.prod_pow]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    rw [← pow_mul, ← pp.group.pow_val_mul]
  have hPair :
      (∏ j, pp.group.pair pp.generator (groupVecMul z M j) ^ (e j).val) =
        pp.group.pair pp.generator (leak G PG zDim κ pp f M x z) := ?_
  swap
  · rw [← hLeak, groupDot_eq, map_prod]
    simp only [map_pow]
  have hNeg :
      (∏ j, (egg ^ (-v (Sum.inr j)).val) ^ (e j).val) =
        (egg ^ (dotProduct (fun j => v (Sum.inr j)) e).val)⁻¹ := ?_
  swap
  · have h := pp.group.groupDot_expVecT egg
      (-(fun j : Fin (n'.eval κ) => v (Sum.inr j))) e
    rw [neg_dotProduct, pp.group.pow_val_neg_GT] at h
    simpa only [groupDot_eq, pp.group.expVecT_apply, Pi.neg_apply] using h
  rw [dec_eq, decFirst_correct, decSecond_correct, groupDot_eq,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, rec_output_eq_eval G PG κ pp f x]
  rw [← groupDot_eq (pp.group.expVecT egg (Matrix.vecMul v K)) r]
  change
    (∏ j, (pp.group.pair pp.generator (groupVecMul z M j) *
        egg ^ (-v (Sum.inr j)).val) ^ (e j).val) *
      groupDot (pp.group.expVecT egg (Matrix.vecMul v K)) r =
        pp.group.pair pp.generator (leak G PG zDim κ pp f M x z)
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [hPair, hNeg, pp.group.groupDot_expVecT, hMask]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- The internal raw algorithm bundle inherits perfect correctness for all its draws
[Wee20, §4.2, p. 10, (11)]. It has no efficiency hypothesis.

**Proof sketch.** Read `scheme_raw_eq` to expose its four cores, then apply `pi_dec_eq`. -/
theorem scheme_raw_correct (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    let S := scheme_raw G PG zDim κ pp
    S.dec f M x (S.keyCore (S.setupCore a).2 f M t)
        (S.encCore (S.setupCore a).1 x (pp.group.expVec pp.generator z) s) =
      pp.group.pair pp.generator (leak G PG zDim κ pp f M x z) := by
  simpa only [scheme_raw_eq] using (pi_dec_eq G PG zDim κ pp f M x z a s t)

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
