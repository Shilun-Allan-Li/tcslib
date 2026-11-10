/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SIS parameters and the short integer kernel relation

## Main definitions

* `TCSlib.Cryptography.SIS.Parameters`: dimensions, modulus, and squared Euclidean bound.
* `IsSolution`: a nonzero short integer vector annihilated by the matrix modulo its modulus.

## Main results

* `isSolution_iff` exposes the nonzero, squared-norm and kernel conditions.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.1.1.

**Deviation.** The bound is an integer bound on the squared Euclidean norm, explicitly
named `sqNormBound`, instead of a real bound on the Euclidean norm. Matrices have `n`
rows and `m` columns. No assumption about existence of short solutions, hardness, or a
connection with LWE is part of the numeric bundle or the solution relation.
-/

namespace TCSlib.Cryptography.SIS

/-- Numeric SIS parameters: a matrix with `dimension` rows and `columns` columns modulo
`modulus >= 2`, and an integer upper bound on squared Euclidean solution norm
[Pei16, Definition 4.1.1, squared-bound formulation]. -/
structure Parameters where
  /-- The number of rows of the public matrix. -/
  dimension : ℕ
  /-- The number of columns, hence coordinates of a solution. -/
  columns : ℕ
  /-- The modulus of the kernel equation. -/
  modulus : ℕ
  /-- The allowed upper bound on `sum_i z_i^2`. -/
  sqNormBound : ℕ
  /-- The modulus is at least two. -/
  modulus_ge_two : 2 ≤ modulus

instance (P : Parameters) : NeZero P.modulus :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ 1) P.modulus_ge_two)⟩

/-- An SIS solution is an integer vector that is nonzero over the integers, has squared
Euclidean norm at most `sqNormBound`, and maps to zero under the matrix modulo the
modulus [Pei16, Definition 4.1.1, squared-bound formulation]. Nonzeroness is deliberately
not tested after reduction modulo the modulus. -/
def IsSolution (P : Parameters)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (z : Fin P.columns → ℤ) : Prop :=
  z ≠ 0 ∧ (∑ i, z i ^ 2) ≤ (P.sqNormBound : ℤ) ∧
    A.mulVec (fun i => (z i : ZMod P.modulus)) = 0

/-- The SIS relation holds exactly when the integer vector is nonzero, its sum of
squared coordinates is bounded, and its reduction lies in the matrix's modular kernel. -/
theorem isSolution_iff (P : Parameters)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (z : Fin P.columns → ℤ) :
    IsSolution P A z ↔ z ≠ 0 ∧ (∑ i, z i ^ 2) ≤ (P.sqNormBound : ℤ) ∧
      A.mulVec (fun i => (z i : ZMod P.modulus)) = 0 := Iff.rfl

end TCSlib.Cryptography.SIS
