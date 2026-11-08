<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.pre_mdetPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory choice independence

**Claim.** Replacing memory instructions by either of two fixed Boolean return instructions leaves the precondition unchanged.

**Proof.** If the configuration is halted, both preconditions agree immediately. At a live control state, inspect the memory program's instruction. If it is a deterministic register instruction, either deterministic part retains it (`Complexity.LogProg.MARM.detPart_det`), so the preconditions coincide. For any memory instruction, each deterministic part instead returns its chosen Boolean (`Complexity.LogProg.MARM.detPart_mem`). The precondition for a return instruction is true, independent of that Boolean, so the two preconditions still agree.

**Key facts.** `Complexity.LogProg.MARM.detPart_det`, `Complexity.LogProg.MARM.detPart_mem`.
