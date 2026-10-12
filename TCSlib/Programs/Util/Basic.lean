/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Util/Basic.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Util/Basic.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# What most files use of Mathlib

The order and the absolute value on `ℕ`, `ℤ` and ordered fields, casts between them, and the common
tactics.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/
