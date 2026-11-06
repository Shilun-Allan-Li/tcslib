import TCSlib.Complexity.Promise.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/

/-!
# Promise problems

Promise problems and the promise versions of classical classes, the setting of quantum
complexity [Wat08, §II.1]. Part of the quantum campaign (plan
`campaign/design/plans/QuantumComplexityPlan.md` on branch `quantum/campaign`, item Q0.1).

## Contents

- `Complexity.Promise.Basic`: `Promise.Problem`, `ofLanguage`, promise `P` and promise `BPP`
-/
