/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Assumption
import TCSlib.Cryptography.LWE.BitNoise
import TCSlib.Cryptography.Pseudorandom.Generators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The direct DLWE generator and its entropy budget

## Main definitions

* `generate`: publish the existing `(A, As+e)` sample with the matrix included in the seed.
* `seedBitLength`, `outputBitLength`: exact dyadic bit counts, including all noise seeds.

## Main results

The concrete generator advantage equals the existing DLWE advantage. The fixed-sample
assumption implies pseudorandomness against the existing encoded machine tests.
Cardinality and stretch statements expose the additional entropy requirement.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definition 4.2.3 (the pseudorandom LWE sample distribution).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, 22 January 2026,
  Definition 3.5 (generator distinguishing advantage).

Viewing the DLWE sample map as a generator is a repository adaptation of these
definitions. Seed compression requires the displayed strict entropy inequality;
it does not follow from DLWE alone for an arbitrary finite-noise sampler.
The existing asymptotic PRG type indexes by its exact seed length. These statements
do not hide the separate reindexing, finite-small-length and efficient implementation
obligations needed to construct that type. No PRF-based construction is used.
-/

namespace TCSlib.Cryptography.Pseudorandom.Generators.LWE

open Complexity (NUPPT)
open TCSlib.Cryptography.LWE (Parameters Noise Family)

/-- Publish the matrix and its noisy common-secret product, using exactly the existing
LWE sampler [Pei16, Definition 4.2.3; Gar26, Definition 3.5, adaptation]. -/
def generate (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus) :=
  TCSlib.Cryptography.LWE.sample P χ r

/-- The complete generator map is the original finite-sample LWE map. -/
theorem generate_eq (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    generate P χ r = TCSlib.Cryptography.LWE.sample P χ r := rfl

/-- The generator's concrete advantage is exactly the decisional LWE advantage
[Pei16, Definition 4.2.3; Gar26, Definition 3.5].

**Proof sketch.** Read the public generator and advantage equations. Both experiments
use the same real sampler and the identity on the full independent uniform output. -/
theorem prgAdv_generate {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : Noise)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) → ρ → Bool) :
    prgAdv (generate P χ) D = TCSlib.Cryptography.LWE.decisionAdvantage P χ D := by
  sorry

/-- The fixed-sample DLWE assumption supplies negligible generator advantage for
every existing encoded non-uniform PPT test [Pei16, Definition 4.2.3].

**Proof sketch.** Apply the assumption's public characterization to the same machine,
then rewrite each pointwise advantage with `prgAdv_generate` and `Family.advantageAt_eq`.
This transfers pseudorandomness only; no efficient generator or stretch claim is inferred. -/
theorem pseudorandom_under_DLWE (F : Family)
    (h : TCSlib.Cryptography.LWE.DLWEAssumption F) (D : NUPPT) :
    Negligible (fun κ => prgAdv (generate (F.parameters κ) (F.noise κ))
      (fun x r => D.distinguisherL κ
        (TCSlib.Cryptography.LWE.encodeChallenge (F.parameters κ)
          (F.residueBits.eval κ) x) r)) := by
  sorry

/-- Count the seed bits for the full matrix, one secret, and `t` independent noise
bits per row [Pei16, Definition 4.2.3, explicit entropy accounting]. -/
def seedBitLength (P : Parameters) (width t : ℕ) : ℕ :=
  P.samples * P.dimension * width + P.dimension * width + P.samples * t

/-- The seed budget includes matrix, secret and all scalar-noise seed blocks. -/
theorem seedBitLength_eq (P : Parameters) (width t : ℕ) :
    seedBitLength P width t =
      P.samples * P.dimension * width + P.dimension * width + P.samples * t := rfl

/-- Count the published matrix-and-value bits in the existing challenge encoding. -/
def outputBitLength (P : Parameters) (width : ℕ) : ℕ :=
  P.samples * (P.dimension + 1) * width

/-- The output budget is the full matrix plus one residue value per sample. -/
theorem outputBitLength_eq (P : Parameters) (width : ℕ) :
    outputBitLength P width = P.samples * (P.dimension + 1) * width := rfl

/-- For dyadic residues and explicit `t`-bit noise, the real seed space has exactly
`2^seedBitLength` elements [Pei16, Definition 4.2.3, bit-seed specialization].

**Proof sketch.** Evaluate the finite matrix, vector, Boolean function and product
cardinalities. Substitute `q=2^width` and combine the powers using their natural exponents. -/
theorem seed_cardinality (P : Parameters) (width t : ℕ)
    (hq : P.modulus = 2 ^ width) (f : (Fin t → Bool) → ℤ) :
    Fintype.card (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) ×
        (Fin P.samples → (TCSlib.Cryptography.LWE.bitNoise t f).Coins))) =
      2 ^ seedBitLength P width t := by
  sorry

/-- The full dyadic output space has exactly `2^outputBitLength` elements.

**Proof sketch.** Evaluate the matrix and value-vector cardinalities, substitute
the exact power-of-two modulus, and distribute the natural exponent products. -/
theorem output_cardinality (P : Parameters) (width : ℕ)
    (hq : P.modulus = 2 ^ width) :
    Fintype.card (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) = 2 ^ outputBitLength P width := by
  sorry

/-- Positive stretch is equivalent to paying for the secret and noise from the
published value-vector budget. The matrix is counted on both sides.

**Proof sketch.** Expand both bit counts, distribute the output's multiplication,
and cancel the common nonnegative matrix budget from the strict inequality. -/
theorem stretch_iff (P : Parameters) (width t : ℕ) :
    seedBitLength P width t < outputBitLength P width ↔
      P.dimension * width + P.samples * t < P.samples * width := by
  sorry

end TCSlib.Cryptography.Pseudorandom.Generators.LWE
