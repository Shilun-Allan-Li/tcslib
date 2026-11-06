import TCSlib.Quantum.Basic.Register
import TCSlib.Quantum.Basic.Gates
import TCSlib.Quantum.Basic.ApplyOn
import TCSlib.Quantum.Basic.Measure
import TCSlib.Quantum.Basic.Protocols

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/

/-!
# Quantum basics

Qubits, registers, pure states, elementary gates, gates placed on chosen wires, measurement in
the computational basis, and the first protocols. Phase P1 of the quantum campaign (plan
`campaign/design/plans/QuantumComplexityPlan.md` on branch `quantum/campaign`, item Q1).

## Contents

- `Quantum.Basic.Register`: `Qubit`, `Reg n`, the `Bool` bridge, `Ket` and its constructions
- `Quantum.Basic.Gates`: classical and phase gates; `H`, `X`, `Z`, `S`, `CNOT`, `Toffoli`
- `Quantum.Basic.ApplyOn`: placing a `k`-qubit gate on chosen wires of `n` qubits
- `Quantum.Basic.Measure`: the Born rule and one-wire measurement
- `Quantum.Basic.Protocols`: no-cloning, teleportation, superdense coding
-/
