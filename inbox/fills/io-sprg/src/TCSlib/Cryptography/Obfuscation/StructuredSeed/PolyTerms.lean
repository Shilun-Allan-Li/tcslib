/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.TuringMachine.Encoding
import Mathlib.Algebra.MvPolynomial.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite lists of polynomial terms

## Main definitions

* `PolyTerms`: coefficient-and-variable-word lists, with repetitions representing powers.
* `PolyTerms.denote`: the polynomial denoted by a finite term list.
* `PolyTerms.encTerms`: the explicit list-and-pair binary encoding.
* `PolyTerms.encInt`, `PolyTerms.encFin`: coefficient and finite-coordinate encodings.

## Main results

Owner-side readers expose every new definition.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, Sections 2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Turing

/-- A polynomial term list records a coefficient and a finite variable word for each monomial:
`PolyTerms σ R = List (R × List σ)`. [JLS26, Definition 3.3, p. 10].
Disclosed representation refinement: variable words, with repetitions for powers, replace
abstract polynomial syntax
so Phase B can generate an explicit finite string without choosing a support enumeration. -/
abbrev PolyTerms (σ R : Type) := List (R × List σ)

/-- The term-list type is `List (R × List σ)`; glue. -/
theorem polyTerms_eq (σ R : Type) : PolyTerms σ R = List (R × List σ) := rfl

namespace PolyTerms

/-- The denotation is the sum of coefficient times variable-word product:
`denote ts = ∑ t in ts, C t.1 * ∏ i in t.2, X i`.
[JLS26, Definition 3.3, p. 10]. Disclosed representation refinement: a finite term list is the
generated syntax. -/
noncomputable def denote {σ R : Type} [CommSemiring R] (ts : PolyTerms σ R) :
    MvPolynomial σ R :=
  (ts.map fun t => MvPolynomial.C t.1 *
    (t.2.map fun i => (MvPolynomial.X i : MvPolynomial σ R)).prod).sum

/-- The denotation is the list sum of the encoded monomials; glue. -/
theorem denote_eq {σ R : Type} [CommSemiring R] (ts : PolyTerms σ R) :
    denote ts = (ts.map fun t => MvPolynomial.C t.1 *
      (t.2.map fun i => (MvPolynomial.X i : MvPolynomial σ R)).prod).sum := rfl

/-- An integer is its sign bit followed by the little-endian bits of its absolute value:
`encInt z = decide (z < 0) :: Nat.bits z.natAbs`; glue. -/
def encInt (z : ℤ) : List Bool := decide (z < 0) :: Nat.bits z.natAbs

/-- The signed coefficient encoding is its sign and absolute-value bits; glue. -/
theorem encInt_eq (z : ℤ) : encInt z = decide (z < 0) :: Nat.bits z.natAbs := rfl

/-- A finite coordinate is encoded by its actual natural value, `encFin i = Nat.bits i.val`;
glue. No enumeration or choice is used. -/
def encFin {n : ℕ} (i : Fin n) : List Bool := Nat.bits i.val

/-- The coordinate encoding is `Nat.bits i.val`; glue. -/
theorem encFin_eq {n : ℕ} (i : Fin n) : encFin i = Nat.bits i.val := rfl

/-- A term list is encoded by the existing one-prefixed, zero-terminated list code, with
self-delimiting pairs around every coefficient/variable-word term and every variable code.
[JLS26, Definition 3.3, p. 10]. Disclosed representation refinement: this fixes the output
syntax of efficient
polynomial generation; it uses `BoolCircuit.encodeList` and no classical enumeration. -/
def encTerms {σ R : Type} (encR : R → List Bool) (encVar : σ → List Bool)
    (ts : PolyTerms σ R) : List Bool :=
  BoolCircuit.encodeList
    (fun t => pairEncode
      (pairEncode (encR t.1)
        (BoolCircuit.encodeList (fun i => pairEncode (encVar i) []) t.2)) []) ts

/-- The term encoding is the explicit nested list-and-pair code; glue. -/
theorem encTerms_eq {σ R : Type} (encR : R → List Bool) (encVar : σ → List Bool)
    (ts : PolyTerms σ R) :
    encTerms encR encVar ts = BoolCircuit.encodeList
      (fun t => pairEncode
        (pairEncode (encR t.1)
          (BoolCircuit.encodeList (fun i => pairEncode (encVar i) []) t.2)) []) ts := rfl

end PolyTerms

end TCSlib.Cryptography.Obfuscation.StructuredSeed
