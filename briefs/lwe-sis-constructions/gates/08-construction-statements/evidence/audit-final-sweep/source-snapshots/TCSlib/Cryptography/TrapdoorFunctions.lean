/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.TrapdoorFunctions.Lossy
import TCSlib.Cryptography.TrapdoorFunctions.AllButOne

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cryptographic trapdoor-function constructions

## Contents

* `Lossy`: exact dyadic gadgets, deterministic inversion, image loss and DLWE column hybrids.
* `AllButOne`: anti-cyclic branch matrices and bounded-noise branch injectivity statements.

All nontrivial new statements are admitted for the combined statement audit.
The child modules distinguish actual laws and deterministic mathematics from
efficiency/security endpoints. Source-policy work and user-controlled integration
remain open; this facade claims no completed primitive or CCA2 security.
-/
