/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.Symmetric.Regev

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetric-encryption constructions

## Contents

* `Regev`: direct noisy-inner-product encryption, bounded-error correctness statements
  and the concrete two-DLWE-advantage bound.
-/
