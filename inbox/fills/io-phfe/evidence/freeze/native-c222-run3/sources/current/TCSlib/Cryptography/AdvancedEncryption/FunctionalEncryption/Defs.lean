/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Raw
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Efficient
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Correctness
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Simulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Functional-encryption syntax

## Contents

* `Raw`: function classes, public parameters, and exact algorithm cores and draws.
* `Efficient`: uniform efficiency fields for public-key functional encryption.
* `Correctness`: exact honest experiments and perfect or bounded correctness.
* `Simulator`: stateful raw simulators and their uniform efficiency fields.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definitions 4.1-4.3 and 4.6.
-/
