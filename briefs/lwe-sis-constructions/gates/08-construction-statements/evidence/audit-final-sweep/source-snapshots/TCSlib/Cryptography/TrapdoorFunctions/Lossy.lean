/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Gadget
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Matrix
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concealed-gadget lossy trapdoor functions

## Contents

* `Gadget`: exact dyadic encoding, rounding and binary block gadgets.
* `Matrix`: ordinary secret-matrix cancellation, perfect inversion and lossy image bounds.
* `Experiments`: actual finite-noise column hybrids and explicit DLWE bounds.

All nontrivial new statements are admitted for the combined statement audit.
The child modules distinguish actual laws and deterministic mathematics from
efficiency/security endpoints. Source-policy work and user-controlled integration
remain open; this facade claims no completed primitive or CCA2 security.
-/
