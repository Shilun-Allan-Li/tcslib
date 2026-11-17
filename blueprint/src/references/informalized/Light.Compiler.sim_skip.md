<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.sim_skip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skip Statement Simulation

**Claim.** For any setting, depth, and state, the skip statement simulates execution from the state to itself with cost bound zero.

**Proof.** From any valid starting configuration, leave the machine memory unchanged and take zero machine steps. The program counter and memory therefore remain exactly as they were, so the run ends at the position after skip, whose size is zero. The final memory relation is the starting relation, the step bound is $0$, and agreement outside the writable region holds because the two memories coincide.

**Key facts.** `WordRAM.Steps.refl`, `WordRAM.AgreeOutside.refl`.
