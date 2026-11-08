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
records every consumed bit. These representation and advantage identities are proved below.

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
  rw [generateBits_eq, TCSlib.Cryptography.LWE.encodeChallenge_length, outputBitLength_eq]

/-- The structured fair-bit seed contains exactly the declared number of independent
bits, including all scalar-noise seeds.

**Proof sketch.** Count finite functions and products, then combine powers of two.
No modulus premise is needed because every input factor is already a bit type. -/
theorem bit_seed_cardinality (P : Parameters) (width t : ℕ) :
    Fintype.card ((Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool))) =
      2 ^ seedBitLength P width t := by
  rw [seedBitLength_eq]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  simp only [← pow_mul, ← pow_add]
  congr 1
  ac_rfl

/-- Against a full uniform output word, the explicit bit generator has exactly the
DLWE advantage of the canonically encoded test [Pei16, Definition 4.2.3].

**Proof sketch.** The real side is `acceptProb_sampleFromBits` with encoding composed
into the test. At a dyadic modulus, encoding is a bijection onto all words of the
declared output length: combine the existing faithful challenge encoder's injectivity
with the proved output cardinality, using the concrete word reader. Relabel the ideal
uniform word by that bijection, preserving all test coins. -/
theorem generateBits_advantage {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (width t : ℕ) (hq : P.modulus = 2 ^ width)
    (f : (Fin t → Bool) → ℤ) (D : List Bool → ρ → Bool) :
    distAdv (generateBits P width t f)
      (fun u : Fin (outputBitLength P width) → Bool => List.ofFn u) D =
      TCSlib.Cryptography.LWE.decisionAdvantage P
        (TCSlib.Cryptography.LWE.bitNoise t f)
        (fun x r => D (TCSlib.Cryptography.LWE.encodeChallenge P width x) r) := by
  classical
  let X := Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
    (Fin P.samples → ZMod P.modulus)
  let L := outputBitLength P width
  have hlen (x : X) : (TCSlib.Cryptography.LWE.encodeChallenge P width x).length = L := by
    change (TCSlib.Cryptography.LWE.encodeChallenge P width x).length = outputBitLength P width
    rw [TCSlib.Cryptography.LWE.encodeChallenge_length, outputBitLength_eq]
  let enc : X → Fin L → Bool := fun x i =>
    (TCSlib.Cryptography.LWE.encodeChallenge P width x).get
      (Fin.cast (hlen x).symm i)
  have henc (x : X) : List.ofFn (enc x) =
      TCSlib.Cryptography.LWE.encodeChallenge P width x := by
    exact (List.ofFn_congr (hlen x)
      (TCSlib.Cryptography.LWE.encodeChallenge P width x).get).symm.trans
        (List.ofFn_get _)
  have hinj : Function.Injective enc := by
    intro x y hxy
    apply TCSlib.Cryptography.LWE.encodeChallenge_injective P width hq.le
    calc
      TCSlib.Cryptography.LWE.encodeChallenge P width x = List.ofFn (enc x) := (henc x).symm
      _ = List.ofFn (enc y) := congrArg List.ofFn hxy
      _ = TCSlib.Cryptography.LWE.encodeChallenge P width y := henc y
  have hcard : Fintype.card X = Fintype.card (Fin L → Bool) := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      using output_cardinality P width hq
  let e : X ≃ (Fin L → Bool) := Equiv.ofBijective enc
    ((Fintype.bijective_iff_injective_and_card enc).mpr ⟨hinj, hcard⟩)
  have he (x : X) : List.ofFn (e x) =
      TCSlib.Cryptography.LWE.encodeChallenge P width x := henc x
  have hreal : acceptProb (generateBits P width t f) D =
      acceptProb (TCSlib.Cryptography.LWE.sample P (TCSlib.Cryptography.LWE.bitNoise t f))
        (fun x r => D (TCSlib.Cryptography.LWE.encodeChallenge P width x) r) := by
    simpa only [acceptProb_def, generateBits_eq] using
      (TCSlib.Cryptography.LWE.acceptProb_sampleFromBits P width t hq f
        (fun x r => D (TCSlib.Cryptography.LWE.encodeChallenge P width x) r))
  have hideal : acceptProb (fun u : Fin L → Bool => List.ofFn u) D =
      acceptProb (id : X → X)
        (fun x r => D (TCSlib.Cryptography.LWE.encodeChallenge P width x) r) := by
    rw [← acceptProb_comp_equiv e (fun u : Fin L → Bool => List.ofFn u) D]
    simp only [acceptProb_def, he, id_eq]
  simp only [TCSlib.Cryptography.LWE.decisionAdvantage_eq, distAdv_def, hreal]
  rw [hideal]

end TCSlib.Cryptography.Pseudorandom.Generators.LWE
