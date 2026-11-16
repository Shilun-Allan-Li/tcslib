/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Identity-based encryption

## Contents

* `Defs`: IBE systems, perfect correctness and selective-identity chosen-plaintext security
  (IND-sID-CPA).
* `BonehBoyen`: the Boneh–Boyen BDH-based system (BB1) over a bilinear group generator and its
  correctness.
* `BonehBoyenSecurity`: the paper's simulator as a game, and IND-sID-CPA security of BB1 under
  Decision BDH.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004.
-/
