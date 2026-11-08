/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pseudorandom.Generators.LWE.Basic
import TCSlib.Cryptography.Pseudorandom.Generators.LWE.Bits
import TCSlib.Cryptography.Pseudorandom.Generators.LWE.Flat

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Direct generators from decisional LWE

## Contents

* `Basic`: the structured generator, DLWE pseudorandomness and exact entropy budgets.
* `Bits`: the MSB encoded generator on explicit independent seed blocks.
* `Flat`: a single-word generator built from existing little-endian finite bit equivalences.

All nontrivial new statements are admitted for the combined statement audit.
The child modules distinguish actual laws and deterministic mathematics from
efficiency/security endpoints. Source-policy work and user-controlled integration
remain open; this facade claims no completed primitive or CCA2 security.
-/
