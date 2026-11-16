/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Advanced encryption primitives

Encryption primitives beyond private-key and public-key encryption.

## Contents

* `Homomorphic`: homomorphic encryption; leveled Gentry–Sahai–Waters encryption from LWE.
* `IdentityBased`: identity-based encryption, selective-identity security and the Boneh–Boyen
  system (BB1).

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004.
* [GSW13] C. Gentry, A. Sahai, B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, CRYPTO 2013; author version
  dated 8 June 2013.
-/
