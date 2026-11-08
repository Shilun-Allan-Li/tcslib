<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.mstep_det -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Instruction Step

**Claim.** If the instruction at state $l$ is deterministic, then one memory-augmented step from state $l$ leaves the memory state unchanged and agrees with one step of the deterministic part of the program.

**Proof.** Write the memory state as a tape and head position. By hypothesis, the instruction at $l$ is the deterministic instruction $i$. The definition of a memory-augmented step applies $i$ to the register-machine configuration and leaves the tape and head position untouched. The deterministic part also uses $i$ at $l$, by the fact that it preserves deterministic instructions (MARM.detPart_det). Thus both transitions produce the same register-machine configuration, with the original memory state retained.

**Key facts.** `Complexity.LogProg.MARM.detPart_det`.
