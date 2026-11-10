/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Hashing.FromDiscreteLog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cryptographic hashing constructions

## Contents

* `CollisionResistant` — the machine-level hash family interface, compression, and collision game.
* `FromDiscreteLog` — the discrete-log hash family, efficient evaluator and security statement.

`Authentication.Signatures.HashAndSign` consumes the hash interface to extend a signature
scheme's message space. The hash domain and digest width conditions are stated there.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 140.1, Protocol 142.2 and Theorem 142.3.
-/
