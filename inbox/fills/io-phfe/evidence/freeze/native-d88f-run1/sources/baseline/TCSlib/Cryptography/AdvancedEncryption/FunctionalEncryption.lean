/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Run
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Classes
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling

import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key partially hiding functional encryption

## Contents

* `Defs`: generic function classes, raw algorithms, correctness and efficient interfaces.
* `Run`: deterministic bounded stateful oracle runs.
* `Classes`: polynomial public computation and quadratic private computation.
* `PartialGarbling`: corrected arithmetic partial garbling with exact privacy.
* `Simulation`, `SemiAdaptive`: exact stateful simulation games in both adversarial orders.
* `Wee20`: explicit PHFE algorithms, reductions, efficiency targets and assembled headlines.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  Definitions 4.1-4.3 and 4.6, and Section 9.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive, Report 2020/1420, Sections 2-4.
-/
