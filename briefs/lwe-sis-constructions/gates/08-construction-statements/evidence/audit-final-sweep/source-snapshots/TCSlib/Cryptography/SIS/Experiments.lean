/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SIS.Basic
import TCSlib.Cryptography.Foundations.Probability
import Mathlib.Data.Matrix.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The concrete SIS success experiment

## Main definitions

* `TCSlib.Cryptography.SIS.successProbability`: the probability that an adversary
  outputs a valid short, nonzero integer solution for an independent uniform matrix.

## Main results

* `successProbability_eq` exposes the experiment as a uniform probability.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.1.1.

The solver can fail by returning `none`. It otherwise returns an integer vector, not a
vector of residues; validity includes the full integer norm bound and nonzeroness.
There is no restriction on running time in this concrete experiment. No LWE assumption
or lattice reduction is used.
-/

namespace TCSlib.Cryptography.SIS

variable {ρ : Type*} [Fintype ρ]

/-- The SIS success probability samples a uniform public matrix and independent uniform
solver coins, then checks the solver's optional integer vector against `IsSolution`
[Pei16, Definition 4.1.1, squared-bound formulation]. A `none` answer is unsuccessful. -/
noncomputable def successProbability [Nonempty ρ] (P : Parameters)
    (solve : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) →
      ρ → Option (Fin P.columns → ℤ)) : ℝ :=
  uprob fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) × ρ =>
    match solve r.1 r.2 with
    | none => False
    | some z => IsSolution P r.1 z

/-- SIS success is the uniform probability that the optional answer is present and
satisfies the integer solution relation for the sampled matrix. -/
theorem successProbability_eq [Nonempty ρ] (P : Parameters)
    (solve : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) →
      ρ → Option (Fin P.columns → ℤ)) :
    successProbability P solve =
      uprob fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) × ρ =>
        match solve r.1 r.2 with
        | none => False
        | some z => IsSolution P r.1 z := rfl

end TCSlib.Cryptography.SIS
