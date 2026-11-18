/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Group
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Hadamard

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Vectors and matrices in the exponent

The implicit representation `[M]` sends every scalar entry to a power of a supplied group
base. Known scalar vectors and matrices act on group entries through products and powers;
these operations never recover an exponent from a group element. Pairing products implement
matrix multiplication in the target group.

## Main definitions

* `groupDot`, `groupMulVec`, `groupVecMul`: products of known powers of group entries.
* `groupMatMul`, `matMulGroup`: multiplication with a known scalar matrix on either side.
* `BilinearGroup.expVec`, `BilinearGroup.expMat`: source-group implicit representations.
* `BilinearGroup.expVecT`, `BilinearGroup.expMatT`: target-group implicit representations.
* `BilinearGroup.pairVec`, `BilinearGroup.pairMat`, `BilinearGroup.pairTensor`: pairing
  products and entrywise tensor pairings.

## Main results

* `BilinearGroup.expVec_add`, `BilinearGroup.expVec_smul`: scalar arithmetic in the exponent.
* `BilinearGroup.expMat_mulVec`, `BilinearGroup.expVec_vecMul`: matrix actions in the exponent.
* `BilinearGroup.pair_expVec`, `BilinearGroup.pair_expMat`: pairing products evaluate scalar
  dot products and matrix products.
* `BilinearGroup.expVec_tensor_left`, `BilinearGroup.expVec_tensor_right`: tensor products
  with one known scalar factor can be formed in the source group.

The index types are arbitrary finite types. Matrix orientation follows Mathlib: `mulVec`
uses a column vector, while `vecMul` uses a row vector. Thus the row-vector notation of the
source and its transposed column-vector form share the same implicit representation.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020, Cryptology ePrint Archive 2020/1420, §2.1, p. 4 (implicit representation),
  §3.1, p. 6 (tensor products), §4.2, pp. 9–10 (pairing products).
-/

namespace TCSlib.Cryptography.Pairing

open scoped BigOperators Matrix

variable {ι κ υ : Type*} {p : ℕ}

section GroupActions

variable {H : Type*} [CommMonoid H]

/-- Multiply group entries raised to the known scalar coordinates. This is technical glue
for the implicit matrix arithmetic of [Wee20, §2.1, p. 4]. -/
def groupDot [Fintype ι] (v : ι → H) (a : ι → ZMod p) : H :=
  ∏ i, v i ^ (a i).val

/-- `groupDot v a` is the product of the powers `v i ^ (a i).val`. -/
theorem groupDot_eq [Fintype ι] (v : ι → H) (a : ι → ZMod p) :
    groupDot v a = ∏ i, v i ^ (a i).val := rfl

/-- Multiply a group-valued matrix by a known scalar column vector using group operations.
This is the implicit representation of matrix action [Wee20, §2.1, p. 4]. -/
def groupMulVec [Fintype κ] (M : Matrix ι κ H) (a : κ → ZMod p) : ι → H :=
  fun i => groupDot (M i) a

/-- Each coordinate of `groupMulVec M a` is the product of one row's known powers. -/
theorem groupMulVec_apply [Fintype κ] (M : Matrix ι κ H) (a : κ → ZMod p) (i : ι) :
    groupMulVec M a i = groupDot (M i) a := rfl

/-- Multiply a known scalar row vector by a group-valued matrix using group operations.
This follows the row-vector convention of [Wee20, §2.1, p. 4]. -/
def groupVecMul [Fintype ι] (a : ι → ZMod p) (M : Matrix ι κ H) : κ → H :=
  fun j => groupDot (fun i => M i j) a

/-- Each coordinate of `groupVecMul a M` is the product of one column's known powers. -/
theorem groupVecMul_apply [Fintype ι] (a : ι → ZMod p) (M : Matrix ι κ H) (j : κ) :
    groupVecMul a M j = groupDot (fun i => M i j) a := rfl

/-- Multiply a group-valued matrix on the right by a known scalar matrix, using products and
powers only [Wee20, §2.1, p. 4; §4.2, p. 9]. -/
def groupMatMul [Fintype κ] (M : Matrix ι κ H) (N : Matrix κ υ (ZMod p)) :
    Matrix ι υ H := fun i j => groupDot (M i) (fun k => N k j)

/-- An entry of `groupMatMul M N` is the product of powers along the shared index. -/
theorem groupMatMul_apply [Fintype κ] (M : Matrix ι κ H) (N : Matrix κ υ (ZMod p))
    (i : ι) (j : υ) :
    groupMatMul M N i j = groupDot (M i) (fun k => N k j) := rfl

/-- Multiply a group-valued matrix on the left by a known scalar matrix, using products and
powers only [Wee20, §2.1, p. 4; §4.2, p. 10, (12)]. -/
def matMulGroup [Fintype κ] (M : Matrix ι κ (ZMod p)) (N : Matrix κ υ H) :
    Matrix ι υ H := fun i j => groupDot (fun k => N k j) (M i)

/-- An entry of `matMulGroup M N` is the product of the known powers in a column of `N`. -/
theorem matMulGroup_apply [Fintype κ] (M : Matrix ι κ (ZMod p)) (N : Matrix κ υ H)
    (i : ι) (j : υ) :
    matMulGroup M N i j = groupDot (fun k => N k j) (M i) := rfl

end GroupActions

namespace BilinearGroup

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- A source-group vector represents its scalar coordinates as powers of `g`
[Wee20, §2.1, p. 4]. -/
def expVec (g : B.G) (a : ι → ZMod B.order) : ι → B.G := fun i => g ^ (a i).val

/-- A coordinate of the implicit vector is its scalar coordinate exponentiated at `g`. -/
theorem expVec_apply (g : B.G) (a : ι → ZMod B.order) (i : ι) :
    B.expVec g a i = g ^ (a i).val := rfl

/-- A source-group matrix represents its scalar entries as powers of `g`
[Wee20, §2.1, p. 4]. -/
def expMat (g : B.G) (M : Matrix ι κ (ZMod B.order)) : Matrix ι κ B.G :=
  fun i j => g ^ (M i j).val

/-- An entry of the implicit matrix is its scalar entry exponentiated at `g`. -/
theorem expMat_apply (g : B.G) (M : Matrix ι κ (ZMod B.order)) (i : ι) (j : κ) :
    B.expMat g M i j = g ^ (M i j).val := rfl

/-- A target-group vector represents its scalar coordinates as powers of `gT`
[Wee20, §2.1, p. 4]. -/
def expVecT (gT : B.GT) (a : ι → ZMod B.order) : ι → B.GT :=
  fun i => gT ^ (a i).val

/-- A coordinate of the target-group vector is its scalar coordinate raised at `gT`. -/
theorem expVecT_apply (gT : B.GT) (a : ι → ZMod B.order) (i : ι) :
    B.expVecT gT a i = gT ^ (a i).val := rfl

/-- A target-group matrix represents its scalar entries as powers of `gT`
[Wee20, §2.1, p. 4]. -/
def expMatT (gT : B.GT) (M : Matrix ι κ (ZMod B.order)) : Matrix ι κ B.GT :=
  fun i j => gT ^ (M i j).val

/-- An entry of the target-group matrix is its scalar entry exponentiated at `gT`. -/
theorem expMatT_apply (gT : B.GT) (M : Matrix ι κ (ZMod B.order)) (i : ι) (j : κ) :
    B.expMatT gT M i j = gT ^ (M i j).val := rfl

/-- Pair corresponding vector entries and multiply in the target group, implementing the
implicit dot product [Wee20, §2.1, p. 4; §4.2, p. 9, (6)–(8)]. -/
def pairVec [Fintype ι] (a b : ι → B.G) : B.GT := ∏ i, B.pair (a i) (b i)

/-- The vector pairing is the product of the coordinate pairings. -/
theorem pairVec_eq [Fintype ι] (a b : ι → B.G) :
    B.pairVec a b = ∏ i, B.pair (a i) (b i) := rfl

/-- Pair matrix rows against columns and multiply the pairings, implementing matrix
multiplication in the exponent [Wee20, §2.1, p. 4; §4.2, p. 9, (6)–(7)]. -/
def pairMat [Fintype κ] (M : Matrix ι κ B.G) (N : Matrix κ υ B.G) : Matrix ι υ B.GT :=
  fun i j => B.pairVec (M i) (fun k => N k j)

/-- Each entry of the matrix pairing is a row-column vector pairing. -/
theorem pairMat_apply [Fintype κ] (M : Matrix ι κ B.G) (N : Matrix κ υ B.G)
    (i : ι) (j : υ) :
    B.pairMat M N i j = B.pairVec (M i) (fun k => N k j) := rfl

/-- Pair all coordinate pairs of two source-group vectors. This supplies the target-group
representation of their scalar tensor product [Wee20, §3.1, p. 6]. -/
def pairTensor (a : ι → B.G) (b : κ → B.G) : ι × κ → B.GT :=
  fun ij => B.pair (a ij.1) (b ij.2)

/-- A tensor-pairing coordinate is the pairing of its two indexed source-group entries. -/
theorem pairTensor_apply (a : ι → B.G) (b : κ → B.G) (ij : ι × κ) :
    B.pairTensor a b ij = B.pair (a ij.1) (b ij.2) := rfl

/-! ## Scalar arithmetic and implicit vectors -/

/-- Target-group exponents add modulo the group order. Technical glue parallel to
`BilinearGroup.pow_val_add` for the source group; no target-group version is in that API.

**Proof sketch.** Use `ZMod.val_add`, `pow_add`, `pow_mod_card` and `B.card_GT`. -/
theorem pow_val_add_GT (gT : B.GT) (a b : ZMod B.order) :
    gT ^ (a + b).val = gT ^ a.val * gT ^ b.val := sorry

/-- Negating a target-group exponent inverts the group element. Technical glue parallel to
`BilinearGroup.pow_val_neg` for the source group.

**Proof sketch.** Apply `pow_val_add_GT` to `-a` and `a`, whose sum is zero. -/
theorem pow_val_neg_GT (gT : B.GT) (a : ZMod B.order) :
    gT ^ (-a).val = (gT ^ a.val)⁻¹ := sorry

/-- Adding scalar vectors multiplies their implicit source-group vectors
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply the published source-group additive exponent law coordinatewise. -/
theorem expVec_add (g : B.G) (a b : ι → ZMod B.order) :
    B.expVec g (a + b) = B.expVec g a * B.expVec g b := sorry

/-- Negating a scalar vector inverts its implicit source-group vector
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply the published source-group negation law coordinatewise. -/
theorem expVec_neg (g : B.G) (a : ι → ZMod B.order) :
    B.expVec g (-a) = (B.expVec g a)⁻¹ := sorry

/-- Scalar multiplication acts on the implicit vector by known powers
[Wee20, §2.1, p. 4].

**Proof sketch.** Use `pow_val_mul` and `pow_mul` at every coordinate. -/
theorem expVec_smul (g : B.G) (c : ZMod B.order) (a : ι → ZMod B.order) :
    B.expVec g (c • a) = fun i => (B.expVec g a i) ^ c.val := sorry

/-- Adding scalar vectors multiplies their target-group representations
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply `pow_val_add_GT` at every coordinate. -/
theorem expVecT_add (gT : B.GT) (a b : ι → ZMod B.order) :
    B.expVecT gT (a + b) = B.expVecT gT a * B.expVecT gT b := sorry

/-- Negating scalar coordinates inverts the target-group representation
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply `pow_val_neg_GT` at every coordinate. -/
theorem expVecT_neg (gT : B.GT) (a : ι → ZMod B.order) :
    B.expVecT gT (-a) = (B.expVecT gT a)⁻¹ := sorry

/-- A known scalar multiplies target-group exponents through known powers
[Wee20, §2.1, p. 4].

**Proof sketch.** Use `pow_val_mul_GT` and `pow_mul` coordinatewise. -/
theorem expVecT_smul (gT : B.GT) (c : ZMod B.order) (a : ι → ZMod B.order) :
    B.expVecT gT (c • a) = fun i => (B.expVecT gT a i) ^ c.val := sorry

/-- An implicit scalar dot product is a product of known powers of source-group elements
[Wee20, §2.1, p. 4; §4.2, p. 9, (8)].

**Proof sketch.** Induct over the finite index sum, using `pow_val_add`, `pow_val_mul` and
`Finset.prod_pow_eq_pow_sum` to combine the powers. -/
theorem groupDot_expVec [Fintype ι] (g : B.G) (a b : ι → ZMod B.order) :
    groupDot (B.expVec g a) b = g ^ (dotProduct a b).val := sorry

/-- A target-group scalar dot product is a product of known powers
[Wee20, §4.2, p. 9, (8)].

**Proof sketch.** Combine `pow_val_add_GT` and `pow_val_mul_GT` over the finite index sum. -/
theorem groupDot_expVecT [Fintype ι] (gT : B.GT) (a b : ι → ZMod B.order) :
    groupDot (B.expVecT gT a) b = gT ^ (dotProduct a b).val := sorry

/-! ## Matrix actions -/

/-- A known column-vector action commutes with the source-group implicit representation
[Wee20, §2.1, p. 4].

**Proof sketch.** At each row apply `groupDot_expVec` to the defining scalar dot product. -/
theorem expMat_mulVec [Fintype κ] (g : B.G) (M : Matrix ι κ (ZMod B.order))
    (a : κ → ZMod B.order) :
    groupMulVec (B.expMat g M) a = B.expVec g (M *ᵥ a) := sorry

/-- A known row-vector action commutes with the source-group implicit representation
[Wee20, §2.1, p. 4].

**Proof sketch.** At each column apply `groupDot_expVec`, commuting scalar factors. -/
theorem expVec_vecMul [Fintype ι] (g : B.G) (a : ι → ZMod B.order)
    (M : Matrix ι κ (ZMod B.order)) :
    groupVecMul a (B.expMat g M) = B.expVec g (a ᵥ* M) := sorry

/-- A scalar matrix on the right can be applied to a group-valued implicit matrix
[Wee20, §4.2, p. 9, KeyGen].

**Proof sketch.** Apply the vector dot-product law to every row-column entry. -/
theorem expMat_mul [Fintype κ] (g : B.G) (M : Matrix ι κ (ZMod B.order))
    (N : Matrix κ υ (ZMod B.order)) :
    groupMatMul (B.expMat g M) N = B.expMat g (M * N) := sorry

/-- A scalar matrix on the left can be applied to a group-valued implicit matrix
[Wee20, §4.2, p. 10, (12)].

**Proof sketch.** Apply the vector dot-product law entrywise and commute scalar factors. -/
theorem expMat_mul_left [Fintype κ] (g : B.G) (M : Matrix ι κ (ZMod B.order))
    (N : Matrix κ υ (ZMod B.order)) :
    matMulGroup M (B.expMat g N) = B.expMat g (M * N) := sorry

/-- Known powers also implement a target-group matrix-vector action
[Wee20, §4.2, p. 9, (8)].

**Proof sketch.** Apply `groupDot_expVecT` to every row. -/
theorem expMatT_mulVec [Fintype κ] (gT : B.GT) (M : Matrix ι κ (ZMod B.order))
    (a : κ → ZMod B.order) :
    groupMulVec (B.expMatT gT M) a = B.expVecT gT (M *ᵥ a) := sorry

/-! ## Pairings and tensor products -/

/-- Pairing corresponding implicit coordinates evaluates their scalar dot product
[Wee20, §2.1, p. 4; §4.2, p. 9, (6)–(8)].

**Proof sketch.** Apply `bilinear_pow` coordinatewise, reduce products of exponents with
`pow_val_mul_GT`, and combine powers with `pow_val_add_GT`. -/
theorem pair_expVec [Fintype ι] (g h : B.G) (a b : ι → ZMod B.order) :
    B.pairVec (B.expVec g a) (B.expVec h b) = B.pair g h ^ (dotProduct a b).val := sorry

/-- Pairing implicit rows and columns evaluates the scalar matrix product
[Wee20, §2.1, p. 4; §4.2, p. 9, (6)–(7)].

**Proof sketch.** Apply `pair_expVec` to each row-column entry. -/
theorem pair_expMat [Fintype κ] (g h : B.G) (M : Matrix ι κ (ZMod B.order))
    (N : Matrix κ υ (ZMod B.order)) :
    B.pairMat (B.expMat g M) (B.expMat h N) = B.expMatT (B.pair g h) (M * N) := sorry

/-- Tensor pairings expose the product of their scalar coordinates in the target group
[Wee20, §3.1, p. 6].

**Proof sketch.** At each index pair apply `bilinear_pow` and `pow_val_mul_GT`. -/
theorem pairTensor_expVec (g h : B.G) (a : ι → ZMod B.order) (b : κ → ZMod B.order) :
    B.pairTensor (B.expVec g a) (B.expVec h b) =
      B.expVecT (B.pair g h) (fun ij : ι × κ => a ij.1 * b ij.2) := sorry

/-- A tensor product with its right scalar factor known is computable in the source group
[Wee20, §3.3, p. 8, Game 3].

**Proof sketch.** Apply `pow_val_mul` and `pow_mul` at every index pair. -/
theorem expVec_tensor_left (g : B.G) (a : ι → ZMod B.order) (b : κ → ZMod B.order) :
    (fun ij : ι × κ => B.expVec g a ij.1 ^ (b ij.2).val) =
      B.expVec g (fun ij : ι × κ => a ij.1 * b ij.2) := sorry

/-- A tensor product with its left scalar factor known is computable in the source group
[Wee20, §3.3, p. 8, Game 4].

**Proof sketch.** Apply `pow_val_mul`, `pow_mul` and scalar commutativity coordinatewise. -/
theorem expVec_tensor_right (g : B.G) (a : ι → ZMod B.order) (b : κ → ZMod B.order) :
    (fun ij : ι × κ => B.expVec g b ij.2 ^ (a ij.1).val) =
      B.expVec g (fun ij : ι × κ => a ij.1 * b ij.2) := sorry

end BilinearGroup

end TCSlib.Cryptography.Pairing
