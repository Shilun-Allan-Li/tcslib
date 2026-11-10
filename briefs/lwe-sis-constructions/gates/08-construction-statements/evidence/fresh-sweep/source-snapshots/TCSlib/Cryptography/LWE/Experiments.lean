/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Basic
import TCSlib.Cryptography.Foundations.Experiments
import Mathlib.Data.Matrix.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The concrete decisional LWE experiment

## Main definitions

* `TCSlib.Cryptography.LWE.decisionAdvantage`: distinguishing the LWE sample map from
  an independent uniform matrix and value vector.

## Main results

* `decisionAdvantage_eq` exposes the experiment through the existing `distAdv` interface.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.2.3.

The noise is the finite-seed law of `Noise`. No running time or hardness assumption is
imposed here: the distinguisher is any function with finite nonempty independent coins.
The identity sampler on the comparison space makes both the matrix and value vector
uniform and independent. In the real sampler all rows use one common secret.
-/

namespace TCSlib.Cryptography.LWE

variable {ρ : Type*} [Fintype ρ]

/-- The decisional LWE advantage is the absolute difference of acceptance probabilities
on `(A, A s + e)` and an independent uniform `(A, u)` [Pei16, Definition 4.2.3]. The
uniform input to the real sampler independently selects its matrix, one common secret,
and one scalar-noise seed per row. No efficiency restriction is imposed on `D`. -/
noncomputable def decisionAdvantage [Nonempty ρ] (P : Parameters) (χ : Noise)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) → ρ → Bool) : ℝ :=
  distAdv (sample P χ)
    (id : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) → _) D

/-- The LWE advantage compares `sample P χ` with the identity sampler on the full
matrix-and-value space, using the existing distinguishing-advantage experiment. -/
theorem decisionAdvantage_eq [Nonempty ρ] (P : Parameters) (χ : Noise)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) → ρ → Bool) :
    decisionAdvantage P χ D = distAdv (sample P χ)
      (id : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
        (Fin P.samples → ZMod P.modulus)) → _) D := rfl

end TCSlib.Cryptography.LWE
