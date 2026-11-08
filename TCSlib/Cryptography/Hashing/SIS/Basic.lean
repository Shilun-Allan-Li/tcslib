/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SIS.Basic
import Mathlib.Data.Fintype.BigOperators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary matrix hashing and collision differences

## Main definitions

* `hash`: multiply a binary input vector by the public modular matrix.
* `collisionDifference`: subtract the two binary inputs over the integers.

## Main results

The statement-phase obligations bound the difference's squared norm, turn a collision
into an SIS solution, and give cardinal compression and solution existence by pigeonhole.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.1.1, Equation (4.1.1) and following observations;
  Section 5.1.

The selected hash has binary domain and a full modular-vector codomain. Its SIS bound
is a squared Euclidean bound. Composite moduli and zero dimensions are permitted under
the explicit hypotheses. No LWE assumption, bridge between assumptions, generic CRH
interface or efficient machine implementation is introduced.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open TCSlib.Cryptography.SIS (Parameters IsSolution)

/-- The binary matrix hash sends `x` to `A x` modulo the parameter's modulus
[Pei16, Equation (4.1.1), binary-domain restriction]. -/
def hash (P : Parameters)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (x : Fin P.columns → Bool) : Fin P.dimension → ZMod P.modulus :=
  A.mulVec (fun i => ((x i).toNat : ZMod P.modulus))

/-- The hash is the matrix product with the coordinatewise natural casts of the bits. -/
theorem hash_eq (P : Parameters)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (x : Fin P.columns → Bool) :
    hash P A x = A.mulVec (fun i => ((x i).toNat : ZMod P.modulus)) := rfl

/-- Subtract the binary inputs over the integers, before any reduction modulo the
modulus [Pei16, observations after Equation (4.1.1)]. -/
def collisionDifference (P : Parameters) (x y : Fin P.columns → Bool) :
    Fin P.columns → ℤ :=
  fun i => ((x i).toNat : ℤ) - ((y i).toNat : ℤ)

/-- Coordinate `i` of the collision difference is the difference of the two integer bits. -/
theorem collisionDifference_apply (P : Parameters) (x y : Fin P.columns → Bool)
    (i : Fin P.columns) :
    collisionDifference P x y i = ((x i).toNat : ℤ) - ((y i).toNat : ℤ) := rfl

/-- Distinct binary inputs have a nonzero integer difference
[Pei16, observations after Equation (4.1.1)].

**Proof sketch.** If every integer difference were zero, the two integer bit casts
would agree at each coordinate. The two Boolean cases recover equality of the inputs. -/
theorem collisionDifference_ne_zero (P : Parameters) (x y : Fin P.columns → Bool)
    (hxy : x ≠ y) : collisionDifference P x y ≠ 0 := by
  sorry

/-- The squared Euclidean norm of a binary-input difference is at most the number
of columns [Pei16, observations after Equation (4.1.1)].

**Proof sketch.** Each coordinate is minus one, zero or one, hence its square is at
most one. Sum the inequalities over the finite column index. -/
theorem collisionDifference_sqNorm_le (P : Parameters) (x y : Fin P.columns → Bool) :
    (∑ i, collisionDifference P x y i ^ 2) ≤ (P.columns : ℤ) := by
  sorry

/-- A collision between distinct binary inputs yields an SIS solution whenever the
squared-norm budget covers the column count [Pei16, observations after Equation (4.1.1)].

**Proof sketch.** The difference is nonzero and has the preceding norm bound. Cast its
coordinates and use `Matrix.mulVec_sub` to turn equal hashes into the modular kernel
equation. Read all three solution conditions through the existing `SIS.isSolution_iff`. -/
theorem collisionDifference_isSolution (P : Parameters)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (x y : Fin P.columns → Bool) (hxy : x ≠ y) (hhash : hash P A x = hash P A y)
    (hbound : P.columns ≤ P.sqNormBound) :
    IsSolution P A (collisionDifference P x y) := by
  sorry

/-- The full binary domain is strictly larger than the modular-vector codomain
when `q^dimension < 2^columns` [Pei16, observations after Equation (4.1.1)].

**Proof sketch.** Read the cardinalities of finite function spaces, Boolean values and
`ZMod`; these are exactly the two natural-number powers in the hypothesis. -/
theorem cardinal_compression (P : Parameters)
    (hcompress : P.modulus ^ P.dimension < 2 ^ P.columns) :
    Fintype.card (Fin P.dimension → ZMod P.modulus) <
      Fintype.card (Fin P.columns → Bool) := by
  sorry

/-- Every public matrix has a binary collision when the binary domain is larger
than the modular codomain [Pei16, observations after Equation (4.1.1)].

**Proof sketch.** An injective hash would imply that its domain cardinality is at
most its codomain cardinality, contradicting `cardinal_compression`. Extract a pair
of distinct inputs with equal hashes. -/
theorem exists_collision (P : Parameters)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (hcompress : P.modulus ^ P.dimension < 2 ^ P.columns) :
    ∃ x y : Fin P.columns → Bool, x ≠ y ∧ hash P A x = hash P A y := by
  sorry

/-- Compression and a sufficiently large norm budget guarantee an SIS solution
for every matrix [Pei16, observations after Equation (4.1.1)]. This is existence,
not an efficient algorithm or a hardness assertion.

**Proof sketch.** Obtain the binary collision and apply `collisionDifference_isSolution`. -/
theorem exists_solution (P : Parameters)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (hcompress : P.modulus ^ P.dimension < 2 ^ P.columns)
    (hbound : P.columns ≤ P.sqNormBound) : ∃ z, IsSolution P A z := by
  sorry

end TCSlib.Cryptography.Hashing.SIS
