/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Complexity.ClassP.BinaryArith.Mul
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary arithmetic representation adapters

## Main definitions

* `toLE`: reverse a most-significant-bit-first word and normalize the result.
* `normalizeWidthPoly`: pad or truncate an MSB word to a polynomial parameter width.
* `fromLEPoly`: write a little-endian word in the canonical fixed-width MSB format.

## Main results

The semantic equations, exact output widths, normalization and round-trip formulas,
and all three polynomial-time contracts are proved. They handle arbitrary parameter
templates, malformed pairs and zero widths. Complete cryptographic implementations
and primitive-security theorems remain separate consumer obligations.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Section 2.1 (bit-string machine representations).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, Section 7.2 (the surrounding machine model).

**Representation adaptation.** These are technical repository adapters, rather than
textbook arithmetic theorems. Candidates uses fixed-width MSB words; the existing
`Complexity.BinArith` machines use normalized little-endian `Nat.bits` words. Reuse
`BinaryArith.Basic` and `BinaryArith.Mul` for normalization/reversal, the polynomial
cut contracts in `Randomized.Primitives`, and `EnsembleLemmas.polyTimeComputable_zeros`.
No private padding, traversal or arithmetic host is introduced. Their full axiom
dependencies still require the consumer gate; a filled source body alone is not
that certificate.

Parameter templates are arbitrary words: only their lengths matter. Pair projections
are total, so malformed pairs give the width at parameter zero and an empty payload.
Zero widths are allowed. Width normalization keeps the low bits, which differs from
the existing right-padding/prefix convention. No numeric fit premise is needed until
claiming a lossless round trip.
-/

namespace TCSlib.Cryptography.Encoding.BinaryArith

open Complexity Turing
open TCSlib.Cryptography.NumberTheory (listToNat)

/-- Convert an MSB word to normalized little-endian bits by reversing and normalizing
it [PS10, Section 2.1, repository representation adaptation]. -/
def toLE (w : List Bool) : List Bool :=
  Nat.bits (LogProg.bitsVal w.reverse)

/-- `toLE w` is `Nat.bits (LogProg.bitsVal w.reverse)`. -/
theorem toLE_eq (w : List Bool) :
    toLE w = Nat.bits (LogProg.bitsVal w.reverse) := rfl

/-- Conversion produces the normalized little-endian numeral of the MSB word's value.

**Proof sketch.** Prove the endian equality locally by induction on the word using
`NumberTheory.listToNat_nil`, `listToNat_cons`, list reversal equations and
`BinArith.bitsVal_append_singleton`. Apply `Nat.bits` to that equality. -/
theorem toLE_eq_natBits (w : List Bool) :
    toLE w = Nat.bits (listToNat w) := by
  rw [toLE_eq]
  apply congrArg Nat.bits
  induction w with
  | nil =>
      rw [List.reverse_nil, NumberTheory.listToNat_nil]
      exact (BinArith.bitsVal_eq_zero_iff []).2 rfl
  | cons b w ih =>
      rw [List.reverse_cons, BinArith.bitsVal_append_singleton,
        List.length_reverse, ih, NumberTheory.listToNat_cons]
      cases b with
      | false =>
          simp only [Bool.toNat_false, if_neg Bool.false_ne_true,
            Nat.zero_mul, Nat.add_zero, Nat.zero_add]
      | true =>
          simp only [Bool.toNat_true, if_true, Nat.one_mul]
          exact Nat.add_comm _ _

/-- Reading the converted little-endian word recovers the original MSB value.

**Proof sketch.** Use `toLE_eq_natBits` and the existing `LogProg.bitsVal_bits` equation. -/
theorem bitsVal_toLE (w : List Bool) :
    LogProg.bitsVal (toLE w) = listToNat w := by
  rw [toLE_eq_natBits, LogProg.bitsVal_bits]

/-- Converting to a normalized little-endian word never increases its length.

**Proof sketch.** Read `toLE_eq`, apply `BinArith.length_bits_bitsVal_le` to the reversed
word, and use the length equation for reversal. This includes empty and all-zero words. -/
theorem length_toLE_le (w : List Bool) :
    (toLE w).length ≤ w.length := by
  rw [toLE_eq]
  simpa only [List.length_reverse] using
    BinArith.length_bits_bitsVal_le w.reverse

/-- Conversion from MSB to normalized little-endian words is polynomial-time.
This is technical representation infrastructure for the existing machine model.

**Proof sketch.** Compose `BinArith.polyTimeComputable_reverse` with
`BinArith.polyTimeComputable_normBits`; read the normalizer's public contract and
`toLE_eq`. No new machine or host is required. -/
theorem polyTimeComputable_toLE : PolyTimeComputable toLE := by
  have h : PolyTimeComputable
      (fun w => Nat.bits (LogProg.bitsVal w.reverse)) :=
    BinArith.polyTimeComputable_normBits.comp
      BinArith.polyTimeComputable_reverse
  have heq : toLE = (fun w => Nat.bits (LogProg.bitsVal w.reverse)) :=
    funext toLE_eq
  exact heq.symm ▸ h

/-- Normalize the second pair component to `p` evaluated at the first component's
length, by prepending zeros and retaining the low bits
[PS10, Section 2.1, explicit polynomial-width adaptation]. -/
def normalizeWidthPoly (p : PolyExpr) (z : List Bool) : List Bool :=
  (List.replicate (p.eval (pairFstD z).length) false ++ pairSndD z).drop
    (pairSndD z).length

/-- Width normalization prepends the requested number of zeros and drops as many
bits as the original second component has. -/
theorem normalizeWidthPoly_eq (p : PolyExpr) (z : List Bool) :
    normalizeWidthPoly p z =
      (List.replicate (p.eval (pairFstD z).length) false ++ pairSndD z).drop
        (pairSndD z).length := rfl

/-- On an encoded pair, width normalization writes the second word's value at the
width `p.eval u.length`, truncating only high bits when necessary.

**Proof sketch.** Read the pair projections and `normalizeWidthPoly_eq`. Identify an
all-zero word with the zero numeral using the existing numeral round trip and
`Candidates.listToNat_replicate_false`. Apply `Candidates.natToList_zero_append_drop`.
This works for arbitrary payload and target lengths, including zero. -/
theorem normalizeWidthPoly_pairEncode (p : PolyExpr) (u w : List Bool) :
    normalizeWidthPoly p (pairEncode u w) =
      Candidates.natToList (p.eval u.length) (listToNat w) := by
  have hzero :
      Candidates.natToList (p.eval u.length) 0 =
        List.replicate (p.eval u.length) false := by
    simpa only [List.length_replicate, Candidates.listToNat_replicate_false] using
      Candidates.natToList_length_listToNat
        (List.replicate (p.eval u.length) false)
  rw [normalizeWidthPoly_eq, pairFstD_pairEncode,
    pairSndD_pairEncode, ← hzero]
  exact Candidates.natToList_zero_append_drop (p.eval u.length) w

/-- The normalized word has exactly the requested polynomial width on every input.

**Proof sketch.** Read `normalizeWidthPoly_eq` and the public append, replicate and
drop length equations. Natural arithmetic cancels the payload length; no valid-pair
premise or positive-width premise is needed. -/
theorem normalizeWidthPoly_length (p : PolyExpr) (z : List Bool) :
    (normalizeWidthPoly p z).length = p.eval (pairFstD z).length := by
  rw [normalizeWidthPoly_eq, List.length_drop,
    List.length_append, List.length_replicate]
  omega

/-- Width normalization preserves a payload already having the requested width.

**Proof sketch.** Read `normalizeWidthPoly_eq`. The dropped prefix is exactly the
prepended zero word because the two lengths agree; use the public list drop equations. -/
theorem normalizeWidthPoly_of_length_eq (p : PolyExpr) (z : List Bool)
    (h : (pairSndD z).length = p.eval (pairFstD z).length) :
    normalizeWidthPoly p z = pairSndD z := by
  rw [normalizeWidthPoly_eq, h]
  exact List.drop_left' List.length_replicate

/-- Numeric width normalization at a syntactic polynomial width is polynomial-time.

**Proof sketch.** Use `EnsembleLemmas.polyTimeComputable_zeros` on the first projection,
append the payload, and pair that word with the original payload as length template.
Apply `polyTimeComputable_pairDropPoly .var`. On input `pairEncode u w`, the prepared
word has length `3*w.length + p.eval u.length + 2` and the output has the requested
width, so no new padding or cut host is needed. -/
theorem polyTimeComputable_normalizeWidthPoly (p : PolyExpr) :
    PolyTimeComputable (normalizeWidthPoly p) := by
  have hzeros : PolyTimeComputable
      (fun z => List.replicate (p.eval (pairFstD z).length) false) :=
    EnsembleLemmas.polyTimeComputable_zeros p polyTimeComputable_pairFstD
  convert (polyTimeComputable_pairDropPoly .var).comp
    (polyTimeComputable_pairSndD.pairEncode
      (hzeros.append polyTimeComputable_pairSndD)) using 1
  funext z
  simp only [normalizeWidthPoly_eq, Function.comp_apply,
    pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]

/-- Convert the second pair component from little-endian bits to the polynomial-width
MSB format, retaining the first component as the parameter-length template
[PS10, Section 2.1, repository representation adaptation]. -/
def fromLEPoly (p : PolyExpr) (z : List Bool) : List Bool :=
  normalizeWidthPoly p (pairEncode (pairFstD z) ((pairSndD z).reverse))

/-- Reverse conversion reverses the payload, rebuilds a valid pair with the original
parameter template, then applies `normalizeWidthPoly`. -/
theorem fromLEPoly_eq (p : PolyExpr) (z : List Bool) :
    fromLEPoly p z =
      normalizeWidthPoly p (pairEncode (pairFstD z) ((pairSndD z).reverse)) := rfl

/-- On an encoded pair, reverse conversion writes the little-endian payload's value
at width `p.eval u.length`, allowing normalization and truncation.

**Proof sketch.** Read `fromLEPoly_eq`, the pair equations and
`normalizeWidthPoly_pairEncode`. Derive the reverse endian equality from
`toLE_eq_natBits` applied to the reversed word and `LogProg.bitsVal_bits`;
do not duplicate the endian induction. -/
theorem fromLEPoly_pairEncode (p : PolyExpr) (u w : List Bool) :
    fromLEPoly p (pairEncode u w) =
      Candidates.natToList (p.eval u.length) (LogProg.bitsVal w) := by
  have hvalue : listToNat w.reverse = LogProg.bitsVal w := by
    have h := congrArg LogProg.bitsVal (toLE_eq_natBits w.reverse)
    simp only [toLE_eq, List.reverse_reverse, LogProg.bitsVal_bits] at h
    exact h.symm
  rw [fromLEPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    normalizeWidthPoly_pairEncode, hvalue]

/-- Reverse conversion has exactly the requested width on every input.

**Proof sketch.** Read `fromLEPoly_eq`, apply `normalizeWidthPoly_length`, and read the
first projection of the reconstructed pair. Malformed original inputs remain total. -/
theorem fromLEPoly_length (p : PolyExpr) (z : List Bool) :
    (fromLEPoly p z).length = p.eval (pairFstD z).length := by
  rw [fromLEPoly_eq, normalizeWidthPoly_length, pairFstD_pairEncode]

/-- Converting an MSB word to normalized little-endian and back gives its width
normalization, without requiring its original length to match the target.

**Proof sketch.** Read `fromLEPoly_pairEncode` and `bitsVal_toLE`; compare the resulting
numeral with `normalizeWidthPoly_pairEncode`. -/
theorem fromLEPoly_toLE (p : PolyExpr) (u w : List Bool) :
    fromLEPoly p (pairEncode u (toLE w)) =
      normalizeWidthPoly p (pairEncode u w) := by
  rw [fromLEPoly_pairEncode, bitsVal_toLE, normalizeWidthPoly_pairEncode]

/-- Converting to little-endian and back recovers the exact MSB word when its length
is the requested polynomial width, including leading zero bits.

**Proof sketch.** Apply `fromLEPoly_toLE` and the length-preserving normalization
theorem, reading the original pair's projections through their public equations. -/
theorem fromLEPoly_toLE_of_length_eq (p : PolyExpr) (u w : List Bool)
    (h : w.length = p.eval u.length) :
    fromLEPoly p (pairEncode u (toLE w)) = w := by
  rw [fromLEPoly_toLE]
  have hlength :
      (pairSndD (pairEncode u w)).length = p.eval (pairFstD (pairEncode u w)).length := by
    simpa only [pairFstD_pairEncode, pairSndD_pairEncode] using h
  simpa only [pairSndD_pairEncode] using
    normalizeWidthPoly_of_length_eq p (pairEncode u w) hlength

/-- Converting a fixed-width MSB output back to little-endian yields the original
payload's value reduced modulo `2^width`, on every input.

**Proof sketch.** Rebuild a pair from the total projections and read
`fromLEPoly_pairEncode`, which already uses the reverse endian equality. Apply
`toLE_eq_natBits` and `Candidates.listToNat_natToList_eq_mod`. No fit or valid-pair
premise is necessary. -/
theorem toLE_fromLEPoly (p : PolyExpr) (z : List Bool) :
    toLE (fromLEPoly p z) =
      Nat.bits (LogProg.bitsVal (pairSndD z) %
        2 ^ (p.eval (pairFstD z).length)) := by
  have hpair :
      fromLEPoly p z =
        fromLEPoly p (pairEncode (pairFstD z) (pairSndD z)) := by
    simp only [fromLEPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [hpair, fromLEPoly_pairEncode, toLE_eq_natBits,
    Candidates.listToNat_natToList_eq_mod]

/-- Conversion from little-endian to a polynomial-width MSB word is polynomial-time.

**Proof sketch.** Reverse the second projection using the existing reversal machine,
pair it with the first projection, and compose with
`polyTimeComputable_normalizeWidthPoly`. Read `fromLEPoly_eq` for functional agreement. -/
theorem polyTimeComputable_fromLEPoly (p : PolyExpr) :
    PolyTimeComputable (fromLEPoly p) := by
  have h : PolyTimeComputable (fun z =>
      normalizeWidthPoly p
        (pairEncode (pairFstD z) ((pairSndD z).reverse))) :=
    (polyTimeComputable_normalizeWidthPoly p).comp
      (polyTimeComputable_pairFstD.pairEncode
        (BinArith.polyTimeComputable_reverse.comp polyTimeComputable_pairSndD))
  have heq : fromLEPoly p = (fun z =>
      normalizeWidthPoly p
        (pairEncode (pairFstD z) ((pairSndD z).reverse))) :=
    funext (fromLEPoly_eq p)
  exact heq.symm ▸ h

end TCSlib.Cryptography.Encoding.BinaryArith
