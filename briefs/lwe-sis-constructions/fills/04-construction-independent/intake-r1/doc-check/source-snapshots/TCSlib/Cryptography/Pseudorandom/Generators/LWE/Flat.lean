/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pseudorandom.Generators.LWE.Basic
import TCSlib.Complexity.Randomized.RandomBits

import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A single-word direct DLWE generator

## Main definitions

* `vectorBitsEquiv`, `matrixBitsEquiv`, `noiseBitsEquiv`: explicit existing bit-block packings.
* `flatSeedEquiv`, `flatOutputEquiv`: combine the independent seed and output components.
* `generateFlat`: run the original DLWE sampler between those two bit equivalences.

## Main results

The generator accepts one word of exactly the full seed budget and outputs one word
of exactly the matrix-and-value budget. Its advantage equals the actual DLWE advantage
of the explicitly re-encoded test. These identities are proved below.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definition 4.2.3.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, 22 January 2026,
  Definition 3.5.

The concrete map uses the existing little-endian finite bit equivalences, not an
arbitrary cardinality-choice bijection. The sibling `Bits` module uses the existing
MSB challenge codec; both conventions are explicit. A uniform parameter schedule,
efficient noise implementation, and the conversion from this parameterization to the
existing exact-seed-indexed asymptotic PRG remain separate obligations.
-/

namespace TCSlib.Cryptography.Pseudorandom.Generators.LWE

open TCSlib.Cryptography.LWE (Parameters)

/-- Pack `length` full-width bit blocks as a residue vector at a dyadic modulus. -/
@[simps (config := { isSimp := false }) apply symm_apply]
def vectorBitsEquiv (P : Parameters) (width length : ℕ) (hq : P.modulus = 2 ^ width) :
    (Fin (length * width) → Bool) ≃ (Fin length → ZMod P.modulus) :=
  (Randomized.blocksEquiv length width).trans
    (Equiv.arrowCongr (Equiv.refl (Fin length))
      ((finCongr hq.symm).trans (ZMod.finEquiv P.modulus).toEquiv))

/-- The complete vector packing composes block packing, the modulus cast and `ZMod.finEquiv`. -/
theorem vectorBitsEquiv_eq (P : Parameters) (width length : ℕ)
    (hq : P.modulus = 2 ^ width) :
    vectorBitsEquiv P width length hq =
      (Randomized.blocksEquiv length width).trans
        (Equiv.arrowCongr (Equiv.refl (Fin length))
          ((finCongr hq.symm).trans (ZMod.finEquiv P.modulus).toEquiv)) := rfl

/-- Pack the matrix portion row by row using existing product-index and curry equivalences. -/
@[simps (config := { isSimp := false }) apply symm_apply]
def matrixBitsEquiv (P : Parameters) (width : ℕ) (hq : P.modulus = 2 ^ width) :
    (Fin (P.samples * P.dimension * width) → Bool) ≃
      Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) :=
  (vectorBitsEquiv P width (P.samples * P.dimension) hq).trans
    ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl (ZMod P.modulus))).trans
      (Equiv.curry (Fin P.samples) (Fin P.dimension) (ZMod P.modulus)))

/-- The complete matrix packing first reads residues, then restores their row/column indices. -/
theorem matrixBitsEquiv_eq (P : Parameters) (width : ℕ) (hq : P.modulus = 2 ^ width) :
    matrixBitsEquiv P width hq =
      (vectorBitsEquiv P width (P.samples * P.dimension) hq).trans
        ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl (ZMod P.modulus))).trans
          (Equiv.curry (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))) := rfl

/-- Partition one noise word into exactly one independent `t`-bit seed per LWE row. -/
@[simps (config := { isSimp := false }) apply symm_apply]
def noiseBitsEquiv (m t : ℕ) :
    (Fin (m * t) → Bool) ≃ (Fin m → Fin t → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin m) (Fin t) Bool)

/-- The complete noise packing only regroups existing bits; it does not resample errors. -/
theorem noiseBitsEquiv_eq (m t : ℕ) :
    noiseBitsEquiv m t =
      (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
        (Equiv.curry (Fin m) (Fin t) Bool) := rfl

/-- Split one flat seed into the matrix, common secret and all original noise seeds
[Pei16, Definition 4.2.3, explicit bit packing]. -/
@[simps (config := { isSimp := false }) apply symm_apply]
def flatSeedEquiv (P : Parameters) (width t : ℕ) (hq : P.modulus = 2 ^ width) :
    (Fin (P.samples * P.dimension * width + (P.dimension * width + P.samples * t)) → Bool) ≃
      (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
        ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → Fin t → Bool))) :=
  (Fin.appendEquiv (P.samples * P.dimension * width)
    (P.dimension * width + P.samples * t)).symm.trans
    ((matrixBitsEquiv P width hq).prodCongr
      ((Fin.appendEquiv (P.dimension * width) (P.samples * t)).symm.trans
        ((vectorBitsEquiv P width P.dimension hq).prodCongr
          (noiseBitsEquiv P.samples t))))

/-- The complete flat seed equivalence splits the three budgets and applies their packings. -/
theorem flatSeedEquiv_eq (P : Parameters) (width t : ℕ) (hq : P.modulus = 2 ^ width) :
    flatSeedEquiv P width t hq =
      (Fin.appendEquiv (P.samples * P.dimension * width)
        (P.dimension * width + P.samples * t)).symm.trans
        ((matrixBitsEquiv P width hq).prodCongr
          ((Fin.appendEquiv (P.dimension * width) (P.samples * t)).symm.trans
            ((vectorBitsEquiv P width P.dimension hq).prodCongr
              (noiseBitsEquiv P.samples t)))) := rfl

/-- Pack a flat output word as the full matrix followed by an independent value vector. -/
@[simps (config := { isSimp := false }) apply symm_apply]
def flatOutputEquiv (P : Parameters) (width : ℕ) (hq : P.modulus = 2 ^ width) :
    (Fin (P.samples * P.dimension * width + P.samples * width) → Bool) ≃
      (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
        (Fin P.samples → ZMod P.modulus)) :=
  (Fin.appendEquiv (P.samples * P.dimension * width) (P.samples * width)).symm.trans
    ((matrixBitsEquiv P width hq).prodCongr (vectorBitsEquiv P width P.samples hq))

/-- The complete output equivalence independently packs its matrix and value-vector parts. -/
theorem flatOutputEquiv_eq (P : Parameters) (width : ℕ) (hq : P.modulus = 2 ^ width) :
    flatOutputEquiv P width hq =
      (Fin.appendEquiv (P.samples * P.dimension * width) (P.samples * width)).symm.trans
        ((matrixBitsEquiv P width hq).prodCongr (vectorBitsEquiv P width P.samples hq)) := rfl

/-- Generate one flat binary output by unpacking a uniform seed, applying the existing
actual-law DLWE sampler, and repacking its output [Pei16, Definition 4.2.3]. -/
def generateFlat (P : Parameters) (width t : ℕ) (hq : P.modulus = 2 ^ width)
    (f : (Fin t → Bool) → ℤ)
    (r : Fin (P.samples * P.dimension * width + (P.dimension * width + P.samples * t)) → Bool) :
    Fin (P.samples * P.dimension * width + P.samples * width) → Bool :=
  (flatOutputEquiv P width hq).symm
    (generate P (TCSlib.Cryptography.LWE.bitNoise t f) (flatSeedEquiv P width t hq r))

/-- The complete generator applies exactly the specified unpacking, sampler and repacking. -/
theorem generateFlat_eq (P : Parameters) (width t : ℕ) (hq : P.modulus = 2 ^ width)
    (f : (Fin t → Bool) → ℤ)
    (r : Fin (P.samples * P.dimension * width + (P.dimension * width + P.samples * t)) → Bool) :
    generateFlat P width t hq f r = (flatOutputEquiv P width hq).symm
      (generate P (TCSlib.Cryptography.LWE.bitNoise t f) (flatSeedEquiv P width t hq r)) := rfl

/-- Flat generator advantage equals the actual DLWE advantage of the repacked test.

**Proof sketch.** Relabel real seeds with `flatSeedEquiv` and independent uniform
outputs with `flatOutputEquiv`, keeping all distinguisher coins. Then apply the
existing `prgAdv_generate` identity. No property of the noise images is assumed. -/
theorem generateFlat_advantage {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (width t : ℕ) (hq : P.modulus = 2 ^ width)
    (f : (Fin t → Bool) → ℤ)
    (D : (Fin (P.samples * P.dimension * width + P.samples * width) → Bool) → ρ → Bool) :
    prgAdv (generateFlat P width t hq f) D =
      TCSlib.Cryptography.LWE.decisionAdvantage P (TCSlib.Cryptography.LWE.bitNoise t f)
        (fun pk r => D ((flatOutputEquiv P width hq).symm pk) r) := by
  have hG : generateFlat P width t hq f = fun r =>
      (flatOutputEquiv P width hq).symm
        (generate P (TCSlib.Cryptography.LWE.bitNoise t f)
          (flatSeedEquiv P width t hq r)) :=
    funext (generateFlat_eq P width t hq f)
  rw [hG, prgAdv_comp_equiv, ← prgAdv_generate]
  simp only [prgAdv_eq, distAdv_def]
  rw [acceptProb_comp_equiv (flatSeedEquiv P width t hq)]

/-- The flat seed type uses exactly the earlier full seed budget.

**Proof sketch.** Read `seedBitLength_eq` and reassociate natural addition. -/
theorem flat_seed_length (P : Parameters) (width t : ℕ) :
    P.samples * P.dimension * width + (P.dimension * width + P.samples * t) =
      seedBitLength P width t := by
  rw [seedBitLength_eq, Nat.add_assoc]

/-- The flat output type uses exactly the earlier full matrix-and-value budget.

**Proof sketch.** Read `outputBitLength_eq` and distribute natural multiplication. -/
theorem flat_output_length (P : Parameters) (width : ℕ) :
    P.samples * P.dimension * width + P.samples * width = outputBitLength P width := by
  rw [outputBitLength_eq]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul]

end TCSlib.Cryptography.Pseudorandom.Generators.LWE
