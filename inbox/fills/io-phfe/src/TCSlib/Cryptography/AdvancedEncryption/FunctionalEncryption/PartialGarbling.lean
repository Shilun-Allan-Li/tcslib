/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Defs
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.PathAlgebra

import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.PrefixAlgebra

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Arithmetic partial garbling

## Contents

* `PrefixAlgebra`: weighted finite-prefix conservation for exact privacy.
* `PathAlgebra`: weighted endpoint-matrix identities used by the path-sum proofs.

* `Defs`: corrected matrix syntax, exact reconstruction and privacy, and uniform efficiency.
* `Layered`: the polynomial-tensor instance with explicit forward/backward path formulas.

## References

* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted Sums
  from k-Lin*, CRYPTO 2020; full version, Cryptology ePrint Archive, Report 2020/762,
  Lemma 2 and Appendix A, (28)-(32).
* [IW14] Y. Ishai, H. Wee, *Partial Garbling Schemes and Their Applications*, ICALP 2014;
  full version, Cryptology ePrint Archive, Report 2014/995, Definition 1 and Theorem 3.
-/
