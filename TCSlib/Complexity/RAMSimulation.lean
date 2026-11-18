/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.WordSize
import TCSlib.Complexity.RAMSimulation.Sim.Encoding
import TCSlib.Complexity.RAMSimulation.Sim.Startup
import TCSlib.Complexity.RAMSimulation.Sim.Phases
import TCSlib.Complexity.RAMSimulation.Sim.RunEncoding
import TCSlib.Complexity.RAMSimulation.Sim.RunSlices
import TCSlib.Complexity.RAMSimulation.Sim.RunPhase
import TCSlib.Complexity.RAMSimulation.Sim.RunHost
import TCSlib.Complexity.RAMSimulation.Sim.RunSource
import TCSlib.Complexity.RAMSimulation.Sim.RunChoices
import TCSlib.Complexity.RAMSimulation.Sim.RunDriver
import TCSlib.Complexity.RAMSimulation.Sim.RunStep
import TCSlib.Complexity.RAMSimulation.Sim.RunSpace
import TCSlib.Complexity.RAMSimulation.Sim.RunStartup
import TCSlib.Complexity.RAMSimulation.Sim.RunCosts
import TCSlib.Complexity.RAMSimulation.Sim.RunInstruction
import TCSlib.Complexity.RAMSimulation.Sim.RunPrefix
import TCSlib.Complexity.RAMSimulation.Sim.RunInduction
import TCSlib.Complexity.RAMSimulation.Sim.RunBounds
import TCSlib.Complexity.RAMSimulation.Sim.RunInput
import TCSlib.Complexity.RAMSimulation.Sim.RunBranch
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
- `RAMSimulation.Sim.RunEncoding`, `RAMSimulation.Sim.RunSlices`,
  `RAMSimulation.Sim.RunPhase`: encoding transport and the two fixed choice slices
- `RAMSimulation.Sim.RunHost`, `RAMSimulation.Sim.RunStep`,
  `RAMSimulation.Sim.RunStartup`: the finite position/parity host and its phase executions
- `RAMSimulation.Sim.RunChoices`, `RAMSimulation.Sim.RunSource`,
  `RAMSimulation.Sim.RunDriver`: timed branch words and consumed source coins
- `RAMSimulation.Sim.RunSpace`, `RAMSimulation.Sim.RunCosts`,
  `RAMSimulation.Sim.RunBounds`: common head intervals and the final resource coefficients
- `RAMSimulation.Sim.RunInstruction`, `RAMSimulation.Sim.RunPrefix`,
  `RAMSimulation.Sim.RunInduction`: the shared instruction execution certificate and induction
- `RAMSimulation.Sim.RunInput`, `RAMSimulation.Sim.RunBranch`: completed runs from the input
  and uniform bounds for arbitrary branches
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
