/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Cryptography.LWE.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary encoding of decisional LWE challenges

## Main definitions

* `TCSlib.Cryptography.LWE.encodeChallenge`: the row-major public matrix followed by
  the value vector, with one fixed-width binary numeral per residue.

## Main results

* `encodeChallenge_eq` exposes the concatenation through the common modular encoders.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.2.3.

**Representation convention.** The dimensions and width are fixed by the family at the
security parameter; no delimiters are needed within a challenge. The width must satisfy
`P.modulus <= 2^width` for the encoding to retain all residues. The LWE asymptotic family
carries this bound. The challenge has `P.samples * (P.dimension + 1) * width` bits.
Faithfulness and length are explicit admitted statements below; this module asserts no
efficiency of sampling the mathematical LWE distribution.
-/

namespace TCSlib.Cryptography.LWE

/-- Encode the LWE challenge `(A,b)` of [Pei16, Definition 4.2.3] as the row-major
matrix followed by the value vector. Every entry uses the same fixed width, which is
lossless when `P.modulus <= 2^width`. -/
def encodeChallenge (P : Parameters) (width : ℕ)
    (x : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) : List Bool :=
  Encoding.Modular.encodeMatrix width x.1 ++ Encoding.Modular.encodeVector width x.2

/-- `encodeChallenge P width (A,b)` is `encodeMatrix width A` followed by
`encodeVector width b`. -/
theorem encodeChallenge_eq (P : Parameters) (width : ℕ)
    (x : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) :
    encodeChallenge P width x =
      Encoding.Modular.encodeMatrix width x.1 ++ Encoding.Modular.encodeVector width x.2 := rfl

/-- An encoded LWE challenge contains exactly
`P.samples * (P.dimension + 1) * width` bits [Pei16, Definition 4.2.3, bit accounting].

**Proof sketch.** Add the common encoder's matrix length and value-vector length,
then distribute multiplication. -/
theorem encodeChallenge_length (P : Parameters) (width : ℕ)
    (x : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) :
    (encodeChallenge P width x).length = P.samples * (P.dimension + 1) * width := by
  sorry

/-- Encoding an LWE challenge is injective if the modulus fits in the residue width.

**Proof sketch.** Split equal strings after the known matrix length. Apply the common
matrix and vector injectivity statements to the two respective segments. -/
theorem encodeChallenge_injective (P : Parameters) (width : ℕ)
    (hwidth : P.modulus ≤ 2 ^ width) :
    Function.Injective (encodeChallenge P width) := by
  sorry

end TCSlib.Cryptography.LWE
