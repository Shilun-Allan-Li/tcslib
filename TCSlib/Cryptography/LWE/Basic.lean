/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Noise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Numeric parameters and the finite-sample LWE map

## Main definitions

* `TCSlib.Cryptography.LWE.Parameters`: dimension, sample count and modulus at least two.
* `noisyValues`: the value vector `A s + e` modulo the modulus.
* `sample`: publish a uniform matrix with noisy values for one common uniform secret.

## Main results

* `noisyValues_apply`, `sample_fst`, `sample_snd` are the owner-side readings of the maps.
* `binaryErrorSum_bound` bounds a binary subset sum of magnitude-bounded errors.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definitions 4.2.1 and 4.2.3 and Section 5.2.1.

**Convention.** Rows are samples, so `A` is `m` by `n` and secrets multiply on the right.
This is the transpose of the row-secret convention in [Pei16]. A uniform seed for `sample`
is a product: the matrix, one secret, and one independent scalar-noise seed per row.
The type permits zero samples for boundary checks; it asserts no hardness or nonvacuity.
-/

namespace TCSlib.Cryptography.LWE

/-- Numeric parameters for `m` LWE samples in dimension `n` modulo `q >= 2`
[Pei16, Definitions 4.2.1 and 4.2.3]. Noise is an explicit separate argument and the
asymptotic security parameter is not identified with any of these three numbers. -/
structure Parameters where
  /-- The dimension of the common secret. -/
  dimension : ℕ
  /-- The number of rows sampled under that same secret. -/
  samples : ℕ
  /-- The modulus of the sample equations. -/
  modulus : ℕ
  /-- The modulus is at least two, excluding the zero and trivial residue rings. -/
  modulus_ge_two : 2 ≤ modulus

instance (P : Parameters) : NeZero P.modulus :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ 1) P.modulus_ge_two)⟩

/-- The LWE value vector is the matrix-secret product plus coordinatewise integer
errors reduced modulo `P.modulus` [Pei16, Definition 4.2.1, transposed convention]. -/
def noisyValues (P : Parameters)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (s : Fin P.dimension → ZMod P.modulus) (e : Fin P.samples → ℤ) :
    Fin P.samples → ZMod P.modulus :=
  A.mulVec s + fun i => (e i : ZMod P.modulus)

/-- Coordinate `i` of the noisy value vector is the inner product of row `i` with
the common secret, plus integer error `e i` reduced modulo the modulus. -/
theorem noisyValues_apply (P : Parameters)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (s : Fin P.dimension → ZMod P.modulus) (e : Fin P.samples → ℤ) (i : Fin P.samples) :
    noisyValues P A s e i = (∑ j, A i j * s j) + (e i : ZMod P.modulus) := rfl

/-- A subset selected by a binary mask has absolute sum at most `m*B` when
each of the `m` integer errors has magnitude at most `B`
[Pei16, Section 5.2.1, deterministic bounded-support specialization].

**Proof sketch.** Apply the triangle inequality to the sum. Every selected error
has magnitude at most `B`, and every unselected term is zero. Sum the uniform
bound over all coordinates. -/
theorem binaryErrorSum_bound {m : ℕ} (e : Fin m → ℤ) (r : Fin m → Bool)
    (B : ℕ) (he : ∀ i, (e i).natAbs ≤ B) :
    (∑ i, e i * ((r i).toNat : ℤ)).natAbs ≤ m * B := by
  calc
    (∑ i, e i * ((r i).toNat : ℤ)).natAbs ≤
        ∑ i : Fin m, (e i * ((r i).toNat : ℤ)).natAbs :=
      Finset.le_sum_of_subadditive Int.natAbs (by decide)
        (fun x y => Int.natAbs_add_le x y) Finset.univ _
    _ ≤ ∑ _i : Fin m, B := by
      apply Finset.sum_le_sum
      intro i _
      cases r i
      · simp only [Bool.toNat_false, Nat.cast_zero, mul_zero, Int.natAbs_zero]
        exact Nat.zero_le B
      · simpa only [Bool.toNat_true, Nat.cast_one, mul_one] using he i
    _ = m * B := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_id]

/-- The LWE sampler publishes `(A, A s + e)` with one common secret for all rows
[Pei16, Definition 4.2.3]. A uniform input chooses the matrix and secret independently
and supplies independent scalar-noise seeds to the rows. -/
def sample (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus) :=
  (r.1, noisyValues P r.1 r.2.1 (fun i => χ.sample (r.2.2 i)))

/-- The public matrix of `sample P χ r` is the matrix component of its seed. -/
theorem sample_fst (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    (sample P χ r).1 = r.1 := rfl

/-- The public values of `sample P χ r` use the single secret `r.2.1` and the scalar
noise sampled independently by the coordinate seeds `r.2.2`. -/
theorem sample_snd (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    (sample P χ r).2 = noisyValues P r.1 r.2.1 (fun i => χ.sample (r.2.2 i)) := rfl

end TCSlib.Cryptography.LWE
