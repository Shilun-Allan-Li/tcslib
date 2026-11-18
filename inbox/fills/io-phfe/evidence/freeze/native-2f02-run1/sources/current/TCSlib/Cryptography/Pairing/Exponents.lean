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
    gT ^ (a + b).val = gT ^ a.val * gT ^ b.val :=
  (congrArg (fun n : ℕ => gT ^ n) (ZMod.val_add a b)).trans
    ((congrArg (fun n : ℕ => gT ^ ((a.val + b.val) % n)) B.card_GT).symm.trans
      ((pow_mod_card gT (a.val + b.val)).trans (pow_add gT a.val b.val)))

/-- Negating a target-group exponent inverts the group element. Technical glue parallel to
`BilinearGroup.pow_val_neg` for the source group.

**Proof sketch.** Apply `pow_val_add_GT` to `-a` and `a`, whose sum is zero. -/
theorem pow_val_neg_GT (gT : B.GT) (a : ZMod B.order) :
    gT ^ (-a).val = (gT ^ a.val)⁻¹ :=
  eq_inv_iff_mul_eq_one.mpr
    ((B.pow_val_add_GT gT (-a) a).symm.trans
      ((congrArg (fun z : ZMod B.order => gT ^ z.val) (neg_add_cancel a)).trans
        ((congrArg (fun n : ℕ => gT ^ n) (ZMod.val_zero (n := B.order))).trans
          (pow_zero gT))))

/-- Adding scalar vectors multiplies their implicit source-group vectors
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply the published source-group additive exponent law coordinatewise. -/
theorem expVec_add (g : B.G) (a b : ι → ZMod B.order) :
    B.expVec g (a + b) = B.expVec g a * B.expVec g b :=
  funext fun i =>
    (B.expVec_apply g (a + b) i).trans
      ((B.pow_val_add g (a i) (b i)).trans
        (congrArg₂ (fun x y : B.G => x * y)
          (B.expVec_apply g a i).symm (B.expVec_apply g b i).symm))

/-- Negating a scalar vector inverts its implicit source-group vector
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply the published source-group negation law coordinatewise. -/
theorem expVec_neg (g : B.G) (a : ι → ZMod B.order) :
    B.expVec g (-a) = (B.expVec g a)⁻¹ :=
  funext fun i =>
    (B.expVec_apply g (-a) i).trans
      ((B.pow_val_neg g (a i)).trans
        (congrArg (fun x : B.G => x⁻¹) (B.expVec_apply g a i).symm))

/-- Scalar multiplication acts on the implicit vector by known powers
[Wee20, §2.1, p. 4].

**Proof sketch.** Use `pow_val_mul` and `pow_mul` at every coordinate. -/
theorem expVec_smul (g : B.G) (c : ZMod B.order) (a : ι → ZMod B.order) :
    B.expVec g (c • a) = fun i => (B.expVec g a i) ^ c.val :=
  funext fun i =>
    (show B.expVec g (c • a) i = g ^ (c * a i).val from
      B.expVec_apply g (c • a) i).trans
      ((B.pow_val_mul g c (a i)).trans
        ((congrArg (fun n : ℕ => g ^ n) (Nat.mul_comm c.val (a i).val)).trans
          ((pow_mul g (a i).val c.val).trans
            (congrArg (fun x : B.G => x ^ c.val) (B.expVec_apply g a i).symm))))

/-- Adding scalar vectors multiplies their target-group representations
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply `pow_val_add_GT` at every coordinate. -/
theorem expVecT_add (gT : B.GT) (a b : ι → ZMod B.order) :
    B.expVecT gT (a + b) = B.expVecT gT a * B.expVecT gT b :=
  funext fun i =>
    (B.expVecT_apply gT (a + b) i).trans
      ((B.pow_val_add_GT gT (a i) (b i)).trans
        (congrArg₂ (fun x y : B.GT => x * y)
          (B.expVecT_apply gT a i).symm (B.expVecT_apply gT b i).symm))

/-- Negating scalar coordinates inverts the target-group representation
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply `pow_val_neg_GT` at every coordinate. -/
theorem expVecT_neg (gT : B.GT) (a : ι → ZMod B.order) :
    B.expVecT gT (-a) = (B.expVecT gT a)⁻¹ :=
  funext fun i =>
    (B.expVecT_apply gT (-a) i).trans
      ((B.pow_val_neg_GT gT (a i)).trans
        (congrArg (fun x : B.GT => x⁻¹) (B.expVecT_apply gT a i).symm))

/-- A known scalar multiplies target-group exponents through known powers
[Wee20, §2.1, p. 4].

**Proof sketch.** Use `pow_val_mul_GT` and `pow_mul` coordinatewise. -/
theorem expVecT_smul (gT : B.GT) (c : ZMod B.order) (a : ι → ZMod B.order) :
    B.expVecT gT (c • a) = fun i => (B.expVecT gT a i) ^ c.val :=
  funext fun i =>
    (show B.expVecT gT (c • a) i = gT ^ (c * a i).val from
      B.expVecT_apply gT (c • a) i).trans
      ((B.pow_val_mul_GT gT c (a i)).trans
        ((congrArg (fun n : ℕ => gT ^ n) (Nat.mul_comm c.val (a i).val)).trans
          ((pow_mul gT (a i).val c.val).trans
            (congrArg (fun x : B.GT => x ^ c.val) (B.expVecT_apply gT a i).symm))))

/-- An implicit scalar dot product is a product of known powers of source-group elements
[Wee20, §2.1, p. 4; §4.2, p. 9, (8)].

**Proof sketch.** The local additive exponent homomorphism maps the finite sum to a
product, giving `hSum`. The modular multiplication law gives `hCoordinate`; combine them
with the published product reader. -/
theorem groupDot_expVec [Fintype ι] (g : B.G) (a b : ι → ZMod B.order) :
    groupDot (B.expVec g a) b = g ^ (dotProduct a b).val :=
  let exponentMap : ZMod B.order →+ Additive B.G :=
    { toFun := fun x => Additive.ofMul (g ^ x.val)
      map_zero' :=
        (show Additive.ofMul (g ^ (0 : ZMod B.order).val) = (0 : Additive B.G) from
          congrArg Additive.ofMul
            ((congrArg (fun n : ℕ => g ^ n) (ZMod.val_zero (n := B.order))).trans
              (pow_zero g)))
      map_add' := fun x y =>
        (show Additive.ofMul (g ^ (x + y).val) =
            Additive.ofMul (g ^ x.val) + Additive.ofMul (g ^ y.val) from
          congrArg Additive.ofMul (B.pow_val_add g x y)) }
  have hSum : g ^ (dotProduct a b).val = ∏ i, g ^ (a i * b i).val :=
    (show g ^ (dotProduct a b).val = (∑ i, exponentMap (a i * b i)).toMul from
      congrArg Additive.toMul (map_sum exponentMap (fun i => a i * b i) Finset.univ)).trans
      (show (∑ i, exponentMap (a i * b i)).toMul = ∏ i, g ^ (a i * b i).val from
        toMul_sum Finset.univ (fun i => exponentMap (a i * b i)))
  have hCoordinate : ∀ i, (B.expVec g a i) ^ (b i).val =
      g ^ (a i * b i).val :=
    fun i => (congrArg (fun x : B.G => x ^ (b i).val) (B.expVec_apply g a i)).trans
      ((pow_mul g (a i).val (b i).val).symm.trans (B.pow_val_mul g (a i) (b i)).symm)
  (groupDot_eq (B.expVec g a) b).trans
    ((Finset.prod_congr rfl (fun i _ => hCoordinate i)).trans hSum.symm)

/-- A target-group scalar dot product is a product of known powers
[Wee20, §4.2, p. 9, (8)].

**Proof sketch.** The local target-group exponent homomorphism maps the finite sum to
a product, giving `hSum`. The modular multiplication law gives `hCoordinate`; combine
them with the published product reader. -/
theorem groupDot_expVecT [Fintype ι] (gT : B.GT) (a b : ι → ZMod B.order) :
    groupDot (B.expVecT gT a) b = gT ^ (dotProduct a b).val :=
  let exponentMap : ZMod B.order →+ Additive B.GT :=
    { toFun := fun x => Additive.ofMul (gT ^ x.val)
      map_zero' :=
        (show Additive.ofMul (gT ^ (0 : ZMod B.order).val) = (0 : Additive B.GT) from
          congrArg Additive.ofMul
            ((congrArg (fun n : ℕ => gT ^ n) (ZMod.val_zero (n := B.order))).trans
              (pow_zero gT)))
      map_add' := fun x y =>
        (show Additive.ofMul (gT ^ (x + y).val) =
            Additive.ofMul (gT ^ x.val) + Additive.ofMul (gT ^ y.val) from
          congrArg Additive.ofMul (B.pow_val_add_GT gT x y)) }
  have hSum : gT ^ (dotProduct a b).val = ∏ i, gT ^ (a i * b i).val :=
    (show gT ^ (dotProduct a b).val = (∑ i, exponentMap (a i * b i)).toMul from
      congrArg Additive.toMul (map_sum exponentMap (fun i => a i * b i) Finset.univ)).trans
      (show (∑ i, exponentMap (a i * b i)).toMul = ∏ i, gT ^ (a i * b i).val from
        toMul_sum Finset.univ (fun i => exponentMap (a i * b i)))
  have hCoordinate : ∀ i, (B.expVecT gT a i) ^ (b i).val =
      gT ^ (a i * b i).val :=
    fun i => (congrArg (fun x : B.GT => x ^ (b i).val) (B.expVecT_apply gT a i)).trans
      ((pow_mul gT (a i).val (b i).val).symm.trans (B.pow_val_mul_GT gT (a i) (b i)).symm)
  (groupDot_eq (B.expVecT gT a) b).trans
    ((Finset.prod_congr rfl (fun i _ => hCoordinate i)).trans hSum.symm)

/-! ## Matrix actions -/

/-- A known column-vector action commutes with the source-group implicit representation
[Wee20, §2.1, p. 4].

**Proof sketch.** At each row apply `groupDot_expVec` to the defining scalar dot product. -/
theorem expMat_mulVec [Fintype κ] (g : B.G) (M : Matrix ι κ (ZMod B.order))
    (a : κ → ZMod B.order) :
    groupMulVec (B.expMat g M) a = B.expVec g (M *ᵥ a) :=
  funext fun i =>
    (groupMulVec_apply (B.expMat g M) a i).trans
      ((congrArg (fun row : κ → B.G => groupDot row a)
        (funext fun k => (B.expMat_apply g M i k).trans
          (B.expVec_apply g (M i) k).symm)).trans
        ((B.groupDot_expVec g (M i) a).trans
          (show g ^ (dotProduct (M i) a).val = B.expVec g (M *ᵥ a) i from
            (B.expVec_apply g (M *ᵥ a) i).symm)))

/-- A known row-vector action commutes with the source-group implicit representation
[Wee20, §2.1, p. 4].

**Proof sketch.** At each column apply `groupDot_expVec`, commuting scalar factors. -/
theorem expVec_vecMul [Fintype ι] (g : B.G) (a : ι → ZMod B.order)
    (M : Matrix ι κ (ZMod B.order)) :
    groupVecMul a (B.expMat g M) = B.expVec g (a ᵥ* M) :=
  funext fun j =>
    (groupVecMul_apply a (B.expMat g M) j).trans
      ((congrArg (fun column : ι → B.G => groupDot column a)
        (funext fun i => (B.expMat_apply g M i j).trans
          (B.expVec_apply g (fun i => M i j) i).symm)).trans
        ((B.groupDot_expVec g (fun i => M i j) a).trans
          ((congrArg (fun x : ZMod B.order => g ^ x.val)
            (dotProduct_comm (fun i => M i j) a)).trans
            (show g ^ (dotProduct a (fun i => M i j)).val = B.expVec g (a ᵥ* M) j from
              (B.expVec_apply g (a ᵥ* M) j).symm))))

/-- A scalar matrix on the right can be applied to a group-valued implicit matrix
[Wee20, §4.2, p. 9, KeyGen].

**Proof sketch.** Apply the vector dot-product law to every row-column entry. -/
theorem expMat_mul [Fintype κ] (g : B.G) (M : Matrix ι κ (ZMod B.order))
    (N : Matrix κ υ (ZMod B.order)) :
    groupMatMul (B.expMat g M) N = B.expMat g (M * N) :=
  funext fun i => funext fun j =>
    (groupMatMul_apply (B.expMat g M) N i j).trans
      ((congrArg (fun row : κ → B.G => groupDot row (fun k => N k j))
        (funext fun k => (B.expMat_apply g M i k).trans
          (B.expVec_apply g (M i) k).symm)).trans
        ((B.groupDot_expVec g (M i) (fun k => N k j)).trans
          ((congrArg (fun x : ZMod B.order => g ^ x.val)
            (Matrix.mul_apply' (M := M) (N := N) (i := i) (k := j)).symm).trans
            (B.expMat_apply g (M * N) i j).symm)))

/-- A scalar matrix on the left can be applied to a group-valued implicit matrix
[Wee20, §4.2, p. 10, (12)].

**Proof sketch.** Apply the vector dot-product law entrywise and commute scalar factors. -/
theorem expMat_mul_left [Fintype κ] (g : B.G) (M : Matrix ι κ (ZMod B.order))
    (N : Matrix κ υ (ZMod B.order)) :
    matMulGroup M (B.expMat g N) = B.expMat g (M * N) :=
  funext fun i => funext fun j =>
    (matMulGroup_apply M (B.expMat g N) i j).trans
      ((congrArg (fun column : κ → B.G => groupDot column (M i))
        (funext fun k => (B.expMat_apply g N k j).trans
          (B.expVec_apply g (fun k => N k j) k).symm)).trans
        ((B.groupDot_expVec g (fun k => N k j) (M i)).trans
          ((congrArg (fun x : ZMod B.order => g ^ x.val)
            (dotProduct_comm (fun k => N k j) (M i))).trans
            ((congrArg (fun x : ZMod B.order => g ^ x.val)
              (Matrix.mul_apply' (M := M) (N := N) (i := i) (k := j)).symm).trans
              (B.expMat_apply g (M * N) i j).symm))))

/-- Known powers also implement a target-group matrix-vector action
[Wee20, §4.2, p. 9, (8)].

**Proof sketch.** Apply `groupDot_expVecT` to every row. -/
theorem expMatT_mulVec [Fintype κ] (gT : B.GT) (M : Matrix ι κ (ZMod B.order))
    (a : κ → ZMod B.order) :
    groupMulVec (B.expMatT gT M) a = B.expVecT gT (M *ᵥ a) :=
  funext fun i =>
    (groupMulVec_apply (B.expMatT gT M) a i).trans
      ((congrArg (fun row : κ → B.GT => groupDot row a)
        (funext fun k => (B.expMatT_apply gT M i k).trans
          (B.expVecT_apply gT (M i) k).symm)).trans
        ((B.groupDot_expVecT gT (M i) a).trans
          (show gT ^ (dotProduct (M i) a).val = B.expVecT gT (M *ᵥ a) i from
            (B.expVecT_apply gT (M *ᵥ a) i).symm)))

/-! ## Pairings and tensor products -/

/-- Pairing corresponding implicit coordinates evaluates their scalar dot product
[Wee20, §2.1, p. 4; §4.2, p. 9, (6)–(8)].

**Proof sketch.** Apply `bilinear_pow` coordinatewise, reduce products of exponents with
`pow_val_mul_GT`, and combine powers with `pow_val_add_GT`. -/
theorem pair_expVec [Fintype ι] (g h : B.G) (a b : ι → ZMod B.order) :
    B.pairVec (B.expVec g a) (B.expVec h b) = B.pair g h ^ (dotProduct a b).val :=
  (B.pairVec_eq (B.expVec g a) (B.expVec h b)).trans
    ((Finset.prod_congr rfl (fun i _ =>
      (congrArg₂ (fun u v : B.G => B.pair u v)
        (B.expVec_apply g a i) (B.expVec_apply h b i)).trans
        ((B.bilinear_pow g h (a i).val (b i).val).trans
          ((pow_mul (B.pair g h) (a i).val (b i).val).trans
            (congrArg (fun x : B.GT => x ^ (b i).val)
              (B.expVecT_apply (B.pair g h) a i).symm))))).trans
      ((groupDot_eq (B.expVecT (B.pair g h) a) b).symm.trans
        (B.groupDot_expVecT (B.pair g h) a b)))

/-- Pairing implicit rows and columns evaluates the scalar matrix product
[Wee20, §2.1, p. 4; §4.2, p. 9, (6)–(7)].

**Proof sketch.** Apply `pair_expVec` to each row-column entry. -/
theorem pair_expMat [Fintype κ] (g h : B.G) (M : Matrix ι κ (ZMod B.order))
    (N : Matrix κ υ (ZMod B.order)) :
    B.pairMat (B.expMat g M) (B.expMat h N) = B.expMatT (B.pair g h) (M * N) :=
  funext fun i => funext fun j =>
    (B.pairMat_apply (B.expMat g M) (B.expMat h N) i j).trans
      ((congrArg₂ B.pairVec
        (funext fun k => (B.expMat_apply g M i k).trans
          (B.expVec_apply g (M i) k).symm)
        (funext fun k => (B.expMat_apply h N k j).trans
          (B.expVec_apply h (fun k => N k j) k).symm)).trans
        ((B.pair_expVec g h (M i) (fun k => N k j)).trans
          ((congrArg (fun x : ZMod B.order => B.pair g h ^ x.val)
            (Matrix.mul_apply' (M := M) (N := N) (i := i) (k := j)).symm).trans
            (B.expMatT_apply (B.pair g h) (M * N) i j).symm)))

/-- Tensor pairings expose the product of their scalar coordinates in the target group
[Wee20, §3.1, p. 6].

**Proof sketch.** At each index pair apply `bilinear_pow` and `pow_val_mul_GT`. -/
theorem pairTensor_expVec (g h : B.G) (a : ι → ZMod B.order) (b : κ → ZMod B.order) :
    B.pairTensor (B.expVec g a) (B.expVec h b) =
      B.expVecT (B.pair g h) (fun ij : ι × κ => a ij.1 * b ij.2) :=
  funext fun ij =>
    (B.pairTensor_apply (B.expVec g a) (B.expVec h b) ij).trans
      ((congrArg₂ (fun u v : B.G => B.pair u v)
        (B.expVec_apply g a ij.1) (B.expVec_apply h b ij.2)).trans
        ((B.bilinear_pow g h (a ij.1).val (b ij.2).val).trans
          ((B.pow_val_mul_GT (B.pair g h) (a ij.1) (b ij.2)).symm.trans
            (B.expVecT_apply (B.pair g h)
              (fun ij : ι × κ => a ij.1 * b ij.2) ij).symm)))

/-- A tensor product with its right scalar factor known is computable in the source group
[Wee20, §3.3, p. 8, Game 3].

**Proof sketch.** Apply `pow_val_mul` and `pow_mul` at every index pair. -/
theorem expVec_tensor_left (g : B.G) (a : ι → ZMod B.order) (b : κ → ZMod B.order) :
    (fun ij : ι × κ => B.expVec g a ij.1 ^ (b ij.2).val) =
      B.expVec g (fun ij : ι × κ => a ij.1 * b ij.2) :=
  funext fun ij =>
    (congrArg (fun x : B.G => x ^ (b ij.2).val) (B.expVec_apply g a ij.1)).trans
      ((pow_mul g (a ij.1).val (b ij.2).val).symm.trans
        ((B.pow_val_mul g (a ij.1) (b ij.2)).symm.trans
          (B.expVec_apply g (fun ij : ι × κ => a ij.1 * b ij.2) ij).symm))

/-- A tensor product with its left scalar factor known is computable in the source group
[Wee20, §3.3, p. 8, Game 4].

**Proof sketch.** Apply `pow_val_mul`, `pow_mul` and scalar commutativity coordinatewise. -/
theorem expVec_tensor_right (g : B.G) (a : ι → ZMod B.order) (b : κ → ZMod B.order) :
    (fun ij : ι × κ => B.expVec g b ij.2 ^ (a ij.1).val) =
      B.expVec g (fun ij : ι × κ => a ij.1 * b ij.2) :=
  funext fun ij =>
    (congrArg (fun x : B.G => x ^ (a ij.1).val) (B.expVec_apply g b ij.2)).trans
      ((pow_mul g (b ij.2).val (a ij.1).val).symm.trans
        ((B.pow_val_mul g (b ij.2) (a ij.1)).symm.trans
          ((congrArg (fun z : ZMod B.order => g ^ z.val) (mul_comm (b ij.2) (a ij.1))).trans
            (B.expVec_apply g (fun ij : ι × κ => a ij.1 * b ij.2) ij).symm)))

/-- Pairing a known exponent vector with an arbitrary source-group vector applies
its known scalar weights inside the pairing. This is technical implicit-representation
arithmetic for [Wee20, §2.1, p.4; §4.2, p.9]. No exponents of the arbitrary vector are
chosen.

**Proof sketch.** Read pairVec_eq, expVec_apply and groupDot_eq. The coordinate
identity is pair_pow_left, and map_prod for the existing monoid hom B.pair g moves
the product through the pairing. -/
theorem pairVec_expVec_left [Fintype ι] (g : B.G) (v : ι → ZMod B.order)
    (u : ι → B.G) :
    B.pairVec (B.expVec g v) u = B.pair g (groupDot u v) := by
  simp only [B.pairVec_eq, B.expVec_apply, groupDot_eq, map_prod,
    B.pair_pow_left, B.pair_pow_right]

/-- Successive known scalar row/matrix weights on an arbitrary source-group matrix
compose by ordinary scalar matrix multiplication. This is technical implicit arithmetic
for [Wee20, §2.1, p.4; §4.2, p.9]. The group matrix remains arbitrary.

**Proof sketch.** Read the row/matrix action and product readers, distribute known
powers over products, and interchange the two finite products. At each arbitrary
group entry, apply the published exponent-dot-product law with that entry as base.
Commuting the scalar dot product gives the composed row-matrix weights. -/
theorem groupVecMul_matMulGroup [Fintype ι] [Fintype κ]
    (v : ι → ZMod B.order) (W : Matrix ι κ (ZMod B.order))
    (M : Matrix κ υ B.G) :
    groupVecMul v (matMulGroup W M) = groupVecMul (Matrix.vecMul v W) M := by
  funext j
  simp only [groupVecMul_apply, matMulGroup_apply, groupDot_eq, ← Finset.prod_pow]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro k _
  show (∏ i, (M k j ^ (W i k).val) ^ (v i).val) =
    M k j ^ (dotProduct v (fun i => W i k)).val
  have h := B.groupDot_expVec (M k j) (fun i => W i k) v
  simp only [groupDot_eq, B.expVec_apply] at h
  exact h.trans (congrArg (fun c : ZMod B.order => M k j ^ c.val)
    (dotProduct_comm (fun i => W i k) v))

end BilinearGroup

end TCSlib.Cryptography.Pairing
