import TCSlib.Quantum.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/

/-!
# Quantum computation

Models of quantum computation: states, gates, circuits, the query model, and the algorithms
and nonlocal games built on them. Quantum complexity classes live in
`TCSlib.Complexity.Quantum`. The campaign plan is
`campaign/design/plans/QuantumComplexityPlan.md` on branch `quantum/campaign`.

## Contents

- `Quantum.Basic`: qubits, registers, states, gates, `applyOn`, measurement, first protocols
-/
