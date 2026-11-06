import TCSlib.Complexity.Counting.PP
import TCSlib.Complexity.Counting.GapP
import TCSlib.Complexity.Counting.PolyTime
import TCSlib.Complexity.Counting.Inclusions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/

/-!
# Counting complexity

The class `PP` and gap functions (GapP), with the closure properties that later bound quantum
classes (`BQP ⊆ PP`). Part of the quantum campaign (plan
`campaign/design/plans/QuantumComplexityPlan.md` on branch `quantum/campaign`, items Q0.2–Q0.7
and Q0.9).

## Contents

- `Complexity.Counting.PP`: `InPP`, promise `PP`, `randProb` as a real average
- `Complexity.Counting.GapP`: gaps, verifier combinators, closure hypotheses, GapP closure,
  `PP` through gap functions
- `Complexity.Counting.PolyTime`: the closure hypotheses hold for `polyTimeModel`; the
  certificate verifier
- `Complexity.Counting.Inclusions`: `BPP ⊆ PP`, `PP` closed under complement, `NP ⊆ PP`
-/
