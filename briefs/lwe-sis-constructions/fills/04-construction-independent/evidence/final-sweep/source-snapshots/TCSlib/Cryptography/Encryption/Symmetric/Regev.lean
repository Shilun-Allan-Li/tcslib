/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.Symmetric.Regev.Basic
import TCSlib.Cryptography.Encryption.Symmetric.Regev.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Direct Regev symmetric encryption

## Contents

* `Basic`: mathematical encryption/decryption and bounded-error correctness statements.
* `Experiments`: common-secret sampling and the concrete two-reduction security bound.

The nontrivial results are statement-phase obligations. Efficient uniform algorithms,
the existing `PrivateKeyScheme` bridge and adaptive CPA security remain later work.
-/
