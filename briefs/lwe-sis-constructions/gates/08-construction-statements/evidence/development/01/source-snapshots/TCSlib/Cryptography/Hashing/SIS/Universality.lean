/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.SIS.Basic
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.InformationTheory.LeftoverHash

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Universality and extraction for the existing binary matrix hash

## Main definitions

This module reuses `hash` without defining a second binary matrix hash.

## Main results

Distinct binary inputs have a uniform hash difference even over composite moduli.
The resulting collision universality gives a strong, seed-published leftover-hash
bound with explicit dimension and sample parameters.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Equation (4.1.1) and Section 5.2.1 (the binary linear extractor in Regev encryption).
* [Vad12] S. Vadhan, *Pseudorandomness*, 2012, Theorem 6.18.

No SIS or LWE hardness assumption is used here; the SIS norm field is irrelevant.
The family is collision-universal, not pairwise independent: its zero input always
hashes to zero. All nontrivial statements are admitted. Later proof fills must use
approved owner-side readings of `IsUniversal` and `HasMinEntropy`; the existing
shared-reader proposal remains unapplied in this draft.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open TCSlib.InformationTheory
open TCSlib.Cryptography.SIS (Parameters)

/-- Distinct binary inputs have an exactly uniform modular hash difference for a
uniform matrix [Pei16, Section 5.2.1, regularity argument].

**Proof sketch.** Choose a differing input coordinate. Its integer difference is
`1` or `-1`, hence a unit modulo every allowed modulus. For any assignment of the
other matrix columns, exactly one choice of this column realizes each target
vector. The empty-column case has no distinct inputs. -/
theorem hash_difference_probability (P : Parameters) (x y : Fin P.columns → Bool)
    (hxy : x ≠ y) (z : Fin P.dimension → ZMod P.modulus) :
    uprob (fun A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) =>
      hash P A x - hash P A y = z) = 1 / (P.modulus : ℝ) ^ P.dimension := by
  sorry

/-- The existing binary matrix hash is collision-universal over every allowed modulus
[Pei16, Section 5.2.1; Vad12, Theorem 6.18].

**Proof sketch.** Specialize the uniform-difference equation to zero, rewrite equality
as zero difference, and convert the probability equation to the owner's collision
count bound. No field structure, norm bound or hardness assumption is used. -/
theorem isUniversal_hash (P : Parameters) : IsUniversal (hash P) := by
  sorry

/-- The full uniform distribution on binary words of length `m` has min-entropy `m`
[Vad12, Section 6.1, exact finite uniform specialization].

**Proof sketch.** Every word has probability `1/2^m` by the public uniform probability
equation and the finite function-space cardinality. This is `2^(-m)` over the reals. -/
theorem uniform_bits_hasMinEntropy (m : ℕ) :
    FinDist.HasMinEntropy (FinDist.uniform (Fin m → Bool)) (m : ℝ) := by
  sorry

/-- Publishing the uniform hash seed retains a statistical extraction error at most
`sqrt(q^dimension / 2^columns)/2` [Pei16, Section 5.2.1; Vad12, Theorem 6.18].

**Proof sketch.** Apply the existing strong leftover-hash lemma to `isUniversal_hash`
and uniform binary min-entropy. Evaluate the modular-vector cardinality and convert
the real negative power into division by the positive binary power. -/
theorem strong_leftover_hash (P : Parameters) :
    statDist (hashPair (hash P) (FinDist.uniform (Fin P.columns → Bool)))
      (FinDist.uniform
        (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
          (Fin P.dimension → ZMod P.modulus))) ≤
      (1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns) := by
  sorry

/-- Any independently randomized test of the seed-published hash has at most the
strong leftover-hash distinguishing error [Pei16, Section 5.2.1].

**Proof sketch.** Identify the uniform product seed's pushforward with `hashPair`
through its public probability equation, then apply `distAdv_le_statDist` and
`strong_leftover_hash`. Distinguisher coins remain independent throughout. -/
theorem distAdv_hash_uniform_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters)
    (D : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
      (Fin P.dimension → ZMod P.modulus)) → ρ → Bool) :
    distAdv (fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
      (Fin P.columns → Bool) => (r.1, hash P r.1 r.2))
      (id : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        (Fin P.dimension → ZMod P.modulus)) → _) D ≤
      (1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns) := by
  sorry

/-- A residue width and `2κ` entropy slack give an explicit exponentially small
extraction error [Pei16, Section 5.2.1, quantitative repository refinement].

**Proof sketch.** Bound `q^dimension` by `2^(dimension*width)`. The sample budget
then bounds their ratio by `2^(-2κ)`. Monotonicity of the square root gives the result,
including parameter zero and empty output dimension. -/
theorem leftover_error_le (P : Parameters) (width κ : ℕ)
    (hq : P.modulus ≤ 2 ^ width) (hm : P.dimension * width + 2 * κ ≤ P.columns) :
    (1 / 2 : ℝ) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns) ≤
      (1 / 2 : ℝ) * ((2 : ℝ)⁻¹) ^ κ := by
  sorry

end TCSlib.Cryptography.Hashing.SIS
