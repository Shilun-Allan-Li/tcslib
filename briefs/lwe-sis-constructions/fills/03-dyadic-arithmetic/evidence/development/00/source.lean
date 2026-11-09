/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.BinaryArith
import TCSlib.Complexity.ClassP.BinaryArith.AddSub
import TCSlib.Complexity.ClassP.BinaryArith.Mul
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Scalar arithmetic for dyadic cryptographic encodings

## Main definitions

* `addPoly`: add two MSB operands and write the result at a polynomial width.
* `mulPoly`: multiply two MSB operands and write the result at that width.
* `subPoly`: subtract modulo the corresponding power of two without natural underflow.

## Main results

Canonical writer equations, exact output widths, ring readings and polynomial-time
contracts are statement-phase obligations. Only the three complete defining equations
are proved here. These scalar interfaces do not yet implement a matrix algorithm,
an actual-law sampler or a cryptographic primitive-security endpoint.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Section 2.1 (bit-string machine representations).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, Section 7.2 (the surrounding machine model).

**Representation adaptation.** These are repository scalar adapters, not exact
textbook arithmetic statements. They consume the proved endian/width interfaces in
`Encoding.BinaryArith` and the public canonical-pair equations and machines in
`Complexity.BinArith.AddSub` and `Mul`. No new arithmetic, traversal or padding host
is introduced. Each polynomial is fixed before selecting a machine.

The input layout is `pairEncode u (pairEncode a b)`. Only the length of the arbitrary
template `u` determines the output width. Total default projections cover malformed
pairs; zero widths and overlong operands are allowed. Subtraction first reduces the
right operand to that width, then adds the modulus to the left operand before using
natural subtraction. The modulus word has only one more bit than the output width.
The ring statements also cover width zero, when the modulus is one; cryptographic
parameter consumers supply any stronger modulus premise separately.
-/

namespace TCSlib.Cryptography.Encoding.DyadicArithmetic

open Complexity Turing
open TCSlib.Cryptography.NumberTheory (listToNat)
open TCSlib.Cryptography.Encoding.BinaryArith

/-- Add the two inner MSB operands and write their sum at the polynomial width
determined by the outer template length [PS10, Section 2.1, repository adaptation].
High bits are discarded, implementing addition modulo the corresponding power of two. -/
def addPoly (p : PolyExpr) (z : List Bool) : List Bool :=
  fromLEPoly p
    (pairEncode (pairFstD z)
      (BinArith.add
        (pairEncode
          (toLE (pairFstD (pairSndD z)))
          (toLE (pairSndD (pairSndD z))))))

/-- `addPoly` converts both inner operands, applies the existing binary adder,
and writes its output with the original outer template. -/
theorem addPoly_eq (p : PolyExpr) (z : List Bool) :
    addPoly p z =
      fromLEPoly p
        (pairEncode (pairFstD z)
          (BinArith.add
            (pairEncode
              (toLE (pairFstD (pairSndD z)))
              (toLE (pairSndD (pairSndD z)))))) := rfl

/-- On a nested encoded pair, addition writes the sum of the operand values at
width `p.eval u.length`, allowing arbitrary operand lengths and leading zeros.

**Proof sketch.** Read `addPoly_eq` and the total pair equations. Apply
`toLE_eq_natBits` to both operands and `BinArith.add_pairEncode` to the resulting
canonical pair. Read the outer writer with `fromLEPoly_pairEncode` and
`LogProg.bitsVal_bits`. -/
theorem addPoly_pairEncode (p : PolyExpr) (u a b : List Bool) :
    addPoly p (pairEncode u (pairEncode a b)) =
      Candidates.natToList (p.eval u.length) (listToNat a + listToNat b) := by
  simp only [addPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    toLE_eq_natBits, BinArith.add_pairEncode,
    fromLEPoly_pairEncode, LogProg.bitsVal_bits]

/-- Addition produces exactly the requested width on every raw input, including
malformed outer or inner pairs.

**Proof sketch.** Read `addPoly_eq`, apply `fromLEPoly_length`, and read the first
projection of the reconstructed pair. -/
theorem addPoly_length (p : PolyExpr) (z : List Bool) :
    (addPoly p z).length = p.eval (pairFstD z).length := by
  rw [addPoly_eq, fromLEPoly_length, pairFstD_pairEncode]

/-- The addition output represents the sum of the input values in the residue ring
modulo `2^(p.eval u.length)`, without a fit premise on either operand.

**Proof sketch.** Apply the canonical writer equation and
`Candidates.listToNat_natToList_eq_mod`; remove the remainder under the cast using
`ZMod.natCast_mod` and read the cast of a sum. -/
theorem addPoly_natCast_pairEncode (p : PolyExpr) (u a b : List Bool) :
    (listToNat (addPoly p (pairEncode u (pairEncode a b))) :
        ZMod (2 ^ (p.eval u.length))) =
      (listToNat a : ZMod (2 ^ (p.eval u.length))) +
        (listToNat b : ZMod (2 ^ (p.eval u.length))) := by
  rw [addPoly_pairEncode, Candidates.listToNat_natToList_eq_mod,
    ZMod.natCast_mod, Nat.cast_add]

/-- Scalar addition at any fixed syntactic polynomial width is polynomial-time.

**Proof sketch.** Compose the total projections, `polyTimeComputable_toLE`, pairing,
`BinArith.polyTimeComputable_add`, and `polyTimeComputable_fromLEPoly`. Read
`addPoly_eq` to identify the resulting function. No new machine or host is needed. -/
theorem polyTimeComputable_addPoly (p : PolyExpr) : PolyTimeComputable (addPoly p) := by
  have ha : PolyTimeComputable
      (fun z => toLE (pairFstD (pairSndD z))) :=
    polyTimeComputable_toLE.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have hb : PolyTimeComputable
      (fun z => toLE (pairSndD (pairSndD z))) :=
    polyTimeComputable_toLE.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have h : PolyTimeComputable (fun z =>
      fromLEPoly p
        (pairEncode (pairFstD z)
          (BinArith.add
            (pairEncode
              (toLE (pairFstD (pairSndD z)))
              (toLE (pairSndD (pairSndD z))))))) :=
    (polyTimeComputable_fromLEPoly p).comp
      (polyTimeComputable_pairFstD.pairEncode
        (BinArith.polyTimeComputable_add.comp (ha.pairEncode hb)))
  exact (funext (addPoly_eq p)).symm ▸ h

/-- Multiply the two inner MSB operands and write their product at the polynomial
width determined by the outer template [PS10, Section 2.1, repository adaptation].
The output retains the low bits, implementing multiplication modulo a power of two. -/
def mulPoly (p : PolyExpr) (z : List Bool) : List Bool :=
  fromLEPoly p
    (pairEncode (pairFstD z)
      (BinArith.mul
        (pairEncode
          (toLE (pairFstD (pairSndD z)))
          (toLE (pairSndD (pairSndD z))))))

/-- `mulPoly` converts both inner operands, applies the existing binary multiplier,
and writes its output with the original outer template. -/
theorem mulPoly_eq (p : PolyExpr) (z : List Bool) :
    mulPoly p z =
      fromLEPoly p
        (pairEncode (pairFstD z)
          (BinArith.mul
            (pairEncode
              (toLE (pairFstD (pairSndD z)))
              (toLE (pairSndD (pairSndD z)))))) := rfl

/-- On a nested encoded pair, multiplication writes the product of the operand values
at width `p.eval u.length`, allowing arbitrary operand lengths.

**Proof sketch.** Read `mulPoly_eq` and the total pair equations, convert with
`toLE_eq_natBits`, apply `BinArith.mul_pairEncode`, and read the outer writer using
`fromLEPoly_pairEncode` and `LogProg.bitsVal_bits`. -/
theorem mulPoly_pairEncode (p : PolyExpr) (u a b : List Bool) :
    mulPoly p (pairEncode u (pairEncode a b)) =
      Candidates.natToList (p.eval u.length) (listToNat a * listToNat b) := by
  sorry

/-- Multiplication produces exactly the requested width on every raw input.

**Proof sketch.** Read `mulPoly_eq`, apply `fromLEPoly_length`, and read the first
projection of the reconstructed pair. -/
theorem mulPoly_length (p : PolyExpr) (z : List Bool) :
    (mulPoly p z).length = p.eval (pairFstD z).length := by
  sorry

/-- The multiplication output represents the product in the residue ring modulo
`2^(p.eval u.length)`, without an operand-fit premise.

**Proof sketch.** Read the canonical writer, apply
`Candidates.listToNat_natToList_eq_mod`, then use `ZMod.natCast_mod` and the cast
equation for multiplication. -/
theorem mulPoly_natCast_pairEncode (p : PolyExpr) (u a b : List Bool) :
    (listToNat (mulPoly p (pairEncode u (pairEncode a b))) :
        ZMod (2 ^ (p.eval u.length))) =
      (listToNat a : ZMod (2 ^ (p.eval u.length))) *
        (listToNat b : ZMod (2 ^ (p.eval u.length))) := by
  sorry

/-- Scalar multiplication at any fixed syntactic polynomial width is polynomial-time.

**Proof sketch.** Compose total projections, conversions and pairing with
`BinArith.polyTimeComputable_mul`, then the existing width writer. Read `mulPoly_eq`
for functional agreement; reuse the registered multiplication machinery. -/
theorem polyTimeComputable_mulPoly (p : PolyExpr) : PolyTimeComputable (mulPoly p) := by
  sorry

/-- Subtract the right inner operand modulo the power of two specified by the outer
template [PS10, Section 2.1, repository adaptation]. Reduce the right operand first
and add the modulus to the left operand before natural subtraction, avoiding underflow. -/
def subPoly (p : PolyExpr) (z : List Bool) : List Bool :=
  fromLEPoly p
    (pairEncode (pairFstD z)
      (BinArith.sub
        (pairEncode
          (BinArith.add
            (pairEncode
              (toLE (pairFstD (pairSndD z)))
              (toLE
                ([true] ++ List.replicate (p.eval (pairFstD z).length) false))))
          (toLE
            (normalizeWidthPoly p
              (pairEncode (pairFstD z) (pairSndD (pairSndD z))))))))

/-- `subPoly` normalizes the right operand, adds the binary modulus word to the left
operand, applies the existing natural subtractor, and writes the requested low bits. -/
theorem subPoly_eq (p : PolyExpr) (z : List Bool) :
    subPoly p z =
      fromLEPoly p
        (pairEncode (pairFstD z)
          (BinArith.sub
            (pairEncode
              (BinArith.add
                (pairEncode
                  (toLE (pairFstD (pairSndD z)))
                  (toLE
                    ([true] ++ List.replicate (p.eval (pairFstD z).length) false))))
              (toLE
                (normalizeWidthPoly p
                  (pairEncode (pairFstD z) (pairSndD (pairSndD z)))))))) := rfl

/-- On a nested encoded pair, subtraction writes `A + q - (B mod q)` at width
`p.eval u.length`, where `q` is the corresponding power of two. This is an unconditional
formula for all operand lengths, rather than natural subtraction of the raw values.

**Proof sketch.** Read the own equation and pair projections. The MSB word consisting
of one followed by the polynomial zero word reads as the modulus, using the public
append, singleton and zero-word equations. The right normalizer reads as the right
value modulo that modulus. Convert operands to canonical LE bits, apply the public
addition/subtraction pair equations, and read the outer writer. -/
theorem subPoly_pairEncode (p : PolyExpr) (u a b : List Bool) :
    subPoly p (pairEncode u (pairEncode a b)) =
      Candidates.natToList (p.eval u.length)
        (listToNat a + 2 ^ (p.eval u.length) -
          (listToNat b % 2 ^ (p.eval u.length))) := by
  sorry

/-- Modular subtraction produces exactly the requested width on every raw input.

**Proof sketch.** Read `subPoly_eq`, apply `fromLEPoly_length`, and read the first
projection of the reconstructed pair. Zero width requires no special premise. -/
theorem subPoly_length (p : PolyExpr) (z : List Bool) :
    (subPoly p z).length = p.eval (pairFstD z).length := by
  sorry

/-- The subtraction output represents the ring difference modulo `2^(p.eval u.length)`
for arbitrary operands, including overlong words and width zero.

**Proof sketch.** Apply the canonical writer and remainder-reading equations. The
right remainder is strictly smaller than the positive modulus, so it is at most the
left value plus the modulus. Apply the natural subtraction cast under that bound;
`ZMod.natCast_self` removes the added modulus and `ZMod.natCast_mod` removes the right
remainder. This yields the ring difference without a fit premise. -/
theorem subPoly_natCast_pairEncode (p : PolyExpr) (u a b : List Bool) :
    (listToNat (subPoly p (pairEncode u (pairEncode a b))) :
        ZMod (2 ^ (p.eval u.length))) =
      (listToNat a : ZMod (2 ^ (p.eval u.length))) -
        (listToNat b : ZMod (2 ^ (p.eval u.length))) := by
  sorry

/-- Modular subtraction at any fixed syntactic polynomial width is polynomial-time.

**Proof sketch.** Generate the modulus word by appending a polynomial zero word to
the constant singleton `[true]`, using the existing zeros, constant and append contracts.
Compose conversions, pairing, the proved right normalizer and the existing arithmetic
machines with the width writer. Read `subPoly_eq`. The modulus has polynomial bit
length; no unary modulus, runtime polynomial evaluator or new host is introduced. -/
theorem polyTimeComputable_subPoly (p : PolyExpr) : PolyTimeComputable (subPoly p) := by
  sorry

end TCSlib.Cryptography.Encoding.DyadicArithmetic
