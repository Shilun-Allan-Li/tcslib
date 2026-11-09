/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.Symmetric

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cryptographic encryption constructions

## Contents

* `Symmetric`: direct symmetric-encryption constructions and concrete experiments.

The machine-valued primitive contracts remain owned by `Cryptography.Asymptotic`.
The construction children state their own proof and implementation status.
-/
