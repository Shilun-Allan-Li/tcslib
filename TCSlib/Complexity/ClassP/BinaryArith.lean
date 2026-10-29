/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Iterate
import TCSlib.Complexity.ClassP.BinaryArith.Basic
import TCSlib.Complexity.ClassP.BinaryArith.AddSub
import TCSlib.Complexity.ClassP.BinaryArith.Mul
import TCSlib.Complexity.ClassP.BinaryArith.Div
import TCSlib.Complexity.ClassP.BinaryArith.ModPow
import TCSlib.Complexity.ClassP.BinaryArith.Jacobi
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Complexity.ClassP.BinaryArith.PrimeFind
import TCSlib.Complexity.ClassP.BinaryArith.DetModMath
import TCSlib.Complexity.ClassP.BinaryArith.DetMod

/-!
# Binary arithmetic in polynomial time

Binary arithmetic on `Nat.bits` words (pairs via `Turing.pairEncode`) as polynomial-time
functions: infrastructure for [AB09 §7.2], plus [AB09, Exercise 7.3] and [AB09, §7.2.2].

## Contents

* `Iterate` — iterating a polynomial-time step polynomially often is polynomial-time.
* `Basic` — normalization, last bit, zero-padded bit pairs and finite-state scans.
* `AddSub` — comparison (`<`, `≤`, `=`, also as languages in `P`), addition, subtraction.
* `Mul` — multiplication; word reversal.
* `Div` — quotient and remainder.
* `ModPow` — modular exponentiation [AB09, Exercise 7.3]; the gcd.
* `Jacobi` — the Jacobi symbol for odd moduli [AB09, §7.2.2].
* `Words` — lists of words: map, zip and count loops.
* `Loops` — the counted loop, unary numbers, list lookup, word equality, unary multiplication
  and cutting into blocks.
* `PrimeFind` — the least prime above `2^{⌈log₂ 2n⌉}`, for unary `n`.
* `DetModMath` — the elimination, rotation and zero-column identities over `ZMod p`.
* `DetMod` — the determinant over `ZMod p` by Gaussian elimination.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2; Exercise 7.3.)
-/
