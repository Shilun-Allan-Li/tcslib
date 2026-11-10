/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.TrapdoorFunctions.AllButOne.AntiCyclic
import TCSlib.Cryptography.TrapdoorFunctions.AllButOne.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# All-but-one concealed-gadget functions

## Contents

* `AntiCyclic`: integer branch matrices and power-of-two-width injectivity statements.
* `Basic`: exact lossy-branch cancellation, other-branch injectivity and image bounds.

All nontrivial new statements are admitted for the combined statement audit.
The child modules distinguish actual laws and deterministic mathematics from
efficiency/security endpoints. Source-policy work and user-controlled integration
remain open; this facade claims no completed primitive or CCA2 security.
-/
