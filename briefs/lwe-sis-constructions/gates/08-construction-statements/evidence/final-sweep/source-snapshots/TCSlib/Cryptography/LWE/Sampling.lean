/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.BitNoise
import TCSlib.Cryptography.LWE.Experiments
import TCSlib.Cryptography.Encoding.DyadicUniform

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Actual LWE laws from independent bit blocks

## Main definitions

* `sampleFromBits`: sample a matrix, one common secret, and independent bit-noise seeds.
* `uniformFromBits`: sample an independent full matrix and value vector.

## Main results

The pushforward and acceptance statements identify exactly the existing LWE and
uniform experiments under a dyadic-modulus hypothesis. The noise law remains the
specified `bitNoise`, without a Gaussian or uniform-support substitution.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definitions 4.2.1 and 4.2.3.

This is an explicit fair-bit specialization of the existing finite-noise model.
These statements describe finite maps and laws. Uniform parameter computation,
noise-machine efficiency, and the all-polynomial common-secret sample schedule
are additional obligations, not consequences of exact sampling at one parameter.
-/

namespace TCSlib.Cryptography.LWE

open Encoding.DyadicUniform
open TCSlib.InformationTheory

/-- Apply the existing LWE sample map to disjoint matrix blocks, one secret vector's
blocks, and independent scalar-noise seeds [Pei16, Definition 4.2.3, dyadic adaptation]. -/
def sampleFromBits (P : Parameters) (width t : ℕ) (f : (Fin t → Bool) → ℤ)
    (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool))) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus) :=
  sample P (bitNoise t f)
    (bitsToMatrix width r.1, bitsToVector width r.2.1, r.2.2)

/-- The bit implementation uses the original sample map and the same row-noise seeds. -/
theorem sampleFromBits_eq (P : Parameters) (width t : ℕ) (f : (Fin t → Bool) → ℤ)
    (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool))) :
    sampleFromBits P width t f r = sample P (bitNoise t f)
      (bitsToMatrix width r.1, bitsToVector width r.2.1, r.2.2) := rfl

/-- Uniform independent bit blocks induce exactly the real LWE distribution.

**Proof sketch.** Product the matrix and secret bit-reader bijections, retaining
the noise seed vector by the identity equivalence. Relabel uniform seeds and apply
the public pushforward equation to the original common-secret sampler. -/
theorem sampleFromBits_law (P : Parameters) (width t : ℕ)
    (hq : P.modulus = 2 ^ width) (f : (Fin t → Bool) → ℤ) :
    (FinDist.uniform ((Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool)))).map
      (sampleFromBits P width t f) =
    (FinDist.uniform (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) ×
        (Fin P.samples → (bitNoise t f).Coins)))).map (sample P (bitNoise t f)) := by
  sorry

/-- The exact real-law implementation preserves every independently randomized test.

**Proof sketch.** Use the same product seed equivalence as in `sampleFromBits_law`
and extend it by the identity on the independent distinguisher coins. -/
theorem acceptProb_sampleFromBits {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (width t : ℕ) (hq : P.modulus = 2 ^ width)
    (f : (Fin t → Bool) → ℤ)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) → ρ → Bool) :
    acceptProb (sampleFromBits P width t f) D = acceptProb (sample P (bitNoise t f)) D := by
  sorry

/-- Read independent matrix and value-vector blocks for the comparison distribution
[Pei16, Definition 4.2.3, dyadic adaptation]. -/
def uniformFromBits (P : Parameters) (width : ℕ)
    (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      (Fin P.samples → Fin width → Bool)) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus) :=
  (bitsToMatrix width r.1, bitsToVector width r.2)

/-- The comparison sampler reads the matrix and value vector from disjoint blocks. -/
theorem uniformFromBits_eq (P : Parameters) (width : ℕ)
    (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      (Fin P.samples → Fin width → Bool)) :
    uniformFromBits P width r = (bitsToMatrix width r.1, bitsToVector width r.2) := rfl

/-- The comparison bit sampler induces exactly the independent uniform challenge law.

**Proof sketch.** Take the product of the matrix and value-vector reader bijections.
Its uniform pushforward is the uniform distribution on their product. -/
theorem uniformFromBits_law (P : Parameters) (width : ℕ)
    (hq : P.modulus = 2 ^ width) :
    (FinDist.uniform ((Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      (Fin P.samples → Fin width → Bool))).map (uniformFromBits P width) =
      FinDist.uniform (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
        (Fin P.samples → ZMod P.modulus)) := by
  sorry

end TCSlib.Cryptography.LWE
