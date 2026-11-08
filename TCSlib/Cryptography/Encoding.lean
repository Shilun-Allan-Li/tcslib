/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Cryptography.Encoding.ModularDecode
import TCSlib.Cryptography.Encoding.BinaryArith
import TCSlib.Cryptography.Encoding.DyadicArithmetic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary encodings for cryptographic problem instances

## Contents

* `Modular`: fixed-width modular vector and row-major matrix encodings, their
  defining equations, and their proved length/injectivity guarantees.
* `ModularDecode`: canonical parsers, rejection equations and statement-phase round trips.
* `BinaryArith`: endian and polynomial-width adapter statements for existing binary machines.
* `DyadicArithmetic`: scalar modular addition, multiplication and subtraction statements.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definitions 4.1.1 and 4.2.3.
-/
