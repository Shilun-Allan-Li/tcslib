/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.SIS

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cryptographic hashing constructions

## Contents

* `SIS`: binary matrix hashing, collision-to-SIS statements and a dyadic parameter profile.

This facade introduces no competing generic collision-resistant-hashing contract.
-/
