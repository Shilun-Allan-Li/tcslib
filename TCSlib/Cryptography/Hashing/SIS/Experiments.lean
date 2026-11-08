/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.SIS.Basic
import TCSlib.Cryptography.SIS.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The concrete binary matrix-hash collision reduction

## Main definitions

* `collisionProbability`: success of a typed collision finder on a uniform public matrix.

## Main results

`collisionProbability_le_successProbability` states the direct collision-to-SIS bound.
It is a statement-phase obligation, without a running-time restriction or generic CRH API.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.1.1, observations after Equation (4.1.1); Section 5.1.

The future machine bridge must retain its primitive owner's raw-output padding/splitting
semantics, construct exact signed SIS output, and prove efficiency. Here the collision
finder already returns two typed binary vectors. No LWE hypothesis is used.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open TCSlib.Cryptography.SIS (Parameters)

variable {ρ : Type*} [Fintype ρ] [Nonempty ρ]

/-- Collision probability is the uniform probability that the finder's two binary
outputs are distinct and hash equally [Pei16, observations after Equation (4.1.1)].
The public matrix and the finder's coins are sampled independently. -/
noncomputable def collisionProbability (P : Parameters)
    (find : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) →
      ρ → (Fin P.columns → Bool) × (Fin P.columns → Bool)) : ℝ :=
  uprob fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) × ρ =>
    (find r.1 r.2).1 ≠ (find r.1 r.2).2 ∧
      hash P r.1 (find r.1 r.2).1 = hash P r.1 (find r.1 r.2).2

/-- The collision experiment tests distinctness and hash equality on a uniform
matrix/coin pair. -/
theorem collisionProbability_eq (P : Parameters)
    (find : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) →
      ρ → (Fin P.columns → Bool) × (Fin P.columns → Bool)) :
    collisionProbability P find =
      uprob fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) × ρ =>
        (find r.1 r.2).1 ≠ (find r.1 r.2).2 ∧
          hash P r.1 (find r.1 r.2).1 = hash P r.1 (find r.1 r.2).2 := rfl

/-- The collision finder's success is at most the SIS success of its integer
difference, when the norm budget covers all columns
[Pei16, observations after Equation (4.1.1), explicit probability bound].

**Proof sketch.** Use the same uniform matrix and finder coins in both experiments.
Every successful collision yields `collisionDifference_isSolution`, so its success
event is contained in the solver's event. Apply monotonicity of uniform probability
through the public experiment equations. -/
theorem collisionProbability_le_successProbability (P : Parameters)
    (find : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) →
      ρ → (Fin P.columns → Bool) × (Fin P.columns → Bool))
    (hbound : P.columns ≤ P.sqNormBound) :
    collisionProbability P find ≤
      TCSlib.Cryptography.SIS.successProbability P
        (fun A r => some (collisionDifference P (find A r).1 (find A r).2)) := by
  sorry

end TCSlib.Cryptography.Hashing.SIS
