/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pseudorandom.Generators.LWE.Basic
import TCSlib.Cryptography.LWE.Sampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The DLWE generator on explicit bit blocks

## Main definitions

* `generateBits`: sample from explicit fair-bit blocks and publish the canonical encoding.

## Main results

The output has its exact claimed length and its advantage against a full uniform
output word equals the DLWE advantage of the encoded test. The input cardinality
records every consumed bit. Nontrivial statements await the combined audit.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definition 4.2.3.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, 22 January 2026,
  Definition 3.5.

These structured input blocks are in bijection with words of `seedBitLength` bits.
No efficient flattening/reindexing machine or instance of the existing exact-seed-indexed
asymptotic PRG structure is claimed here. In particular a noise seed's full bit cost
cannot be replaced by the logarithm of its support size without a new sampler proof.
-/

namespace TCSlib.Cryptography.Pseudorandom.Generators.LWE

open TCSlib.Cryptography.LWE (Parameters)

/-- Encode the actual explicit-bit LWE sample as the generator output
[Pei16, Definition 4.2.3; Gar26, Definition 3.5, representation adaptation]. -/
def generateBits (P : Parameters) (width t : ℕ) (f : (Fin t → Bool) → ℤ)
    (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool))) : List Bool :=
  TCSlib.Cryptography.LWE.encodeChallenge P width
    (TCSlib.Cryptography.LWE.sampleFromBits P width t f r)

/-- The bit generator applies exactly the public challenge encoding to its bit sampler. -/
theorem generateBits_eq (P : Parameters) (width t : ℕ) (f : (Fin t → Bool) → ℤ)
    (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool))) :
    generateBits P width t f r = TCSlib.Cryptography.LWE.encodeChallenge P width
      (TCSlib.Cryptography.LWE.sampleFromBits P width t f r) := rfl

/-- Every output has exactly the full matrix-and-value bit length, without a modulus
coverage premise.

**Proof sketch.** Read `generateBits_eq` and the existing `encodeChallenge_length`.
The length is fixed even at a width too small to be faithful. -/
theorem generateBits_length (P : Parameters) (width t : ℕ)
    (f : (Fin t → Bool) → ℤ)
    (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool))) :
    (generateBits P width t f r).length = outputBitLength P width := by
  sorry

/-- The structured fair-bit seed contains exactly the declared number of independent
bits, including all scalar-noise seeds.

**Proof sketch.** Count finite functions and products, then combine powers of two.
No modulus premise is needed because every input factor is already a bit type. -/
theorem bit_seed_cardinality (P : Parameters) (width t : ℕ) :
    Fintype.card ((Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool))) =
      2 ^ seedBitLength P width t := by
  sorry

/-- Against a full uniform output word, the explicit bit generator has exactly the
DLWE advantage of the canonically encoded test [Pei16, Definition 4.2.3].

**Proof sketch.** The real side is `acceptProb_sampleFromBits` with encoding composed
into the test. At a dyadic modulus, encoding is a bijection onto all words of the
declared output length: split matrix and value blocks and apply the dyadic numeral
round trips. Relabel the ideal uniform word by that bijection, preserving test coins. -/
theorem generateBits_advantage {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (width t : ℕ) (hq : P.modulus = 2 ^ width)
    (f : (Fin t → Bool) → ℤ) (D : List Bool → ρ → Bool) :
    distAdv (generateBits P width t f)
      (fun u : Fin (outputBitLength P width) → Bool => List.ofFn u) D =
      TCSlib.Cryptography.LWE.decisionAdvantage P
        (TCSlib.Cryptography.LWE.bitNoise t f)
        (fun x r => D (TCSlib.Cryptography.LWE.encodeChallenge P width x) r) := by
  sorry

end TCSlib.Cryptography.Pseudorandom.Generators.LWE
