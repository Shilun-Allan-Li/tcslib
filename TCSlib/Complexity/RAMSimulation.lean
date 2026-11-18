/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.WordSize
import TCSlib.Complexity.RAMSimulation.Sim.Encoding
import TCSlib.Complexity.RAMSimulation.Sim.Startup
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTable
import TCSlib.Complexity.RAMSimulation.Sim.PhaseLayout
import TCSlib.Complexity.RAMSimulation.Sim.PhaseCore
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTape
import TCSlib.Complexity.RAMSimulation.Sim.PhaseInvariant
import TCSlib.Complexity.RAMSimulation.Sim.PhaseRows
import TCSlib.Complexity.RAMSimulation.Sim.PhaseRegister
import TCSlib.Complexity.RAMSimulation.Sim.PhaseMemory
import TCSlib.Complexity.RAMSimulation.Sim.PhaseInput
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBounds
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBlock
import TCSlib.Complexity.RAMSimulation.Sim.PhaseAtoms
import TCSlib.Complexity.RAMSimulation.Sim.PhaseCompute
import TCSlib.Complexity.RAMSimulation.Sim.PhaseSchedules
import TCSlib.Complexity.RAMSimulation.Sim.PhaseOperations
import TCSlib.Complexity.RAMSimulation.Sim.PhaseControl
import TCSlib.Complexity.RAMSimulation.Sim.PhaseSemantics
import TCSlib.Complexity.RAMSimulation.Sim.PhaseMemoryMachines
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTests
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBranching
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBranchMachines
import TCSlib.Complexity.RAMSimulation.Sim.PhaseHost
import TCSlib.Complexity.RAMSimulation.Sim.PhaseFork
import TCSlib.Complexity.RAMSimulation.Sim.PhaseCoin
import TCSlib.Complexity.RAMSimulation.Sim.PhaseEmit
import TCSlib.Complexity.RAMSimulation.Sim.Phases
import TCSlib.Complexity.RAMSimulation.Simulation
import TCSlib.Complexity.RAMSimulation.Classes

/-!
# Word-RAM programs on Turing machines

Stage 2 of the programming layer (`machine-library-design.md` §15d, backlog PROG-4): one Turing
machine that simulates a program of the extended word RAM (`WordRAM.XInstr`,
`TCSlib/Programs/WordRAM/Extended.lean`), in deterministic and nondeterministic forms, and the
complexity classes that follow from a program's time, cells and word size. The statements passed
their gate on 2026-10-14 (`audits/stage2-statements-findings.md`); their proofs are pending.

## Contents

- `RAMSimulation.WordSize`: the word-size hypothesis `WordRAM.WordSizeComputable` and its two
  bridges (`c · logSpace`, and `c · S` from a space-constructible `S`)
- `RAMSimulation.Sim.Encoding`, `RAMSimulation.Sim.Startup`, `RAMSimulation.Sim.Phases`: the
  simulation's internal interfaces (namespace `WordRAM.Sim`): how eight tapes encode a
  configuration, the start-up, and one phase per instruction
- `RAMSimulation.Sim.PhaseTable`: memory-table lookup and assignment invariants for the phases
- `RAMSimulation.Sim.PhaseLayout`: address ranges and physical memory-table bounds
- `RAMSimulation.Sim.PhaseCore`: finite rows and their framed sequential composition
- `RAMSimulation.Sim.PhaseTape`: tape selection, framing and bounded-run placement
- `RAMSimulation.Sim.PhaseInvariant`: preservation of the encoding by register/table writes
- `RAMSimulation.Sim.PhaseRows`: native constant, arithmetic, half and sign-extension rows
- `RAMSimulation.Sim.PhaseRegister`: register readiness and intermediate frame invariants
- `RAMSimulation.Sim.PhaseMemory`: placed keyed lookup and assignment rows
- `RAMSimulation.Sim.PhaseInput`: placed input-bit access with its input-head endpoint
- `RAMSimulation.Sim.PhaseBounds`: common time and radius allowances for instruction rows
- `RAMSimulation.Sim.PhaseBlock`: certified blocks and tracked register contents
- `RAMSimulation.Sim.PhaseAtoms`: normalized constant and keyed-memory blocks
- `RAMSimulation.Sim.PhaseCompute`: normalized arithmetic, sign-extension and input blocks
- `RAMSimulation.Sim.PhaseSchedules`: immediate fetch, store and binary arithmetic schedules
- `RAMSimulation.Sim.PhaseOperations`: half, input and indirect memory schedules
- `RAMSimulation.Sim.PhaseControl`: fresh entries, choice agreement and live phase exits
- `RAMSimulation.Sim.PhaseSemantics`: matching extended-RAM steps and encoded postconditions
- `RAMSimulation.Sim.PhaseMemoryMachines`: complete deterministic memory-instruction phase certificates
- `RAMSimulation.Sim.PhaseTests`: placed sign and nonzero tests
- `RAMSimulation.Sim.PhaseBranching`: prefixing and wrapping two-exit branch blocks
- `RAMSimulation.Sim.PhaseBranchMachines`: shared operand tests and the signed branch phase
- `RAMSimulation.Sim.PhaseHost`: frame contracts placed through the registered phase host
- `RAMSimulation.Sim.PhaseFork`: two continuations joined at the common next exit
- `RAMSimulation.Sim.PhaseCoin`: the single-choice coin phase
- `RAMSimulation.Sim.PhaseEmit`: optional emission and the complete output phase
- `RAMSimulation.Simulation`: stage 2, `WordRAM.exists_simulation` and
  `WordRAM.exists_ndSimulation`, with their time and space bounds
- `RAMSimulation.Classes`: the nine corollaries (DTIME, P, SPACE, L, log-space transducers,
  Savitch's `SPACE(S·S)` shape, NSPACE and NL)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6, Exercise 1.9; §4.1.)
* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the word RAM
  and the language whose programs stage 2 runs (see `TCSlib/Programs` and the repository NOTICE).
-/
