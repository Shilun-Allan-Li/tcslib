/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Basic
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Regev public-key encryption

## Contents

* `Basic`: mathematical keygen/encryption/decryption and strict bounded-error correctness.
* `Experiments`: explicit DLWE hybrids, binary extraction and quantitative security bounds.

All nontrivial new statements are admitted for the combined statement audit.
The child modules distinguish actual laws and deterministic mathematics from
efficiency/security endpoints. Source-policy work and user-controlled integration
remain open; this facade claims no completed primitive or CCA2 security.
-/
