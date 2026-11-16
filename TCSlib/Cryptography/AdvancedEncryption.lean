/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Advanced encryption primitives

Encryption primitives beyond private-key and public-key encryption.

## Contents

* `Homomorphic`: homomorphic encryption; leveled Gentry–Sahai–Waters encryption from LWE.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, CRYPTO 2013; author version
  dated 8 June 2013.
-/
