/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite-seed integer noise for LWE

## Main definitions

* `TCSlib.Cryptography.LWE.Noise`: a scalar integer sampler on a finite nonempty seed type.
* `Noise.Bounded`: every seed produces an error of absolute value at most a given bound.

## Main results

* `Noise.bounded_iff` reads the support bound without unfolding its predicate.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.2.1.

**Deviation.** This implementation-facing noise model is the pushforward of a uniform
finite seed. It describes finite rational laws, with seed multiplicities retained, and
does not describe an exact infinite discrete Gaussian. No efficient sampler is asserted.
Independent seeds per coordinate specify independent copies of the scalar law.
-/

namespace TCSlib.Cryptography.LWE

/-- A scalar integer error is sampled by applying `sample` to a uniform element of the
finite nonempty type `Coins` [Pei16, Definition 4.2.1, finite-seed specialization].
Repeated images of seeds retain their multiplicities; the law need not be uniform on
the support. This structure asserts neither efficient samplability nor LWE hardness. -/
structure Noise where
  /-- The finite type of seeds, sampled uniformly. -/
  Coins : Type
  /-- The seed type is finite. -/
  [fintype : Fintype Coins]
  /-- The seed type is nonempty, so uniform seeds form a probability distribution. -/
  [nonempty : Nonempty Coins]
  /-- The integer error produced by a seed, before reduction modulo the LWE modulus. -/
  sample : Coins → ℤ

attribute [instance] Noise.fintype Noise.nonempty

namespace Noise

/-- Every seed produces an integer error of absolute value at most `B` [Pei16,
Definition 4.2.1, bounded-noise specialization used for perfect correctness]. -/
def Bounded (χ : Noise) (B : ℕ) : Prop := ∀ r : χ.Coins, (χ.sample r).natAbs ≤ B

/-- The scalar noise is bounded by `B` exactly when every seed's integer error has
natural absolute value at most `B`. -/
theorem bounded_iff (χ : Noise) (B : ℕ) :
    χ.Bounded B ↔ ∀ r : χ.Coins, (χ.sample r).natAbs ≤ B := Iff.rfl

end Noise

end TCSlib.Cryptography.LWE
