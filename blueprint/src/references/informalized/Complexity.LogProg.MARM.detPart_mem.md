<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MARM.detPart_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory Instruction Extraction

**Claim.** If the instruction at a control state is a memory instruction, then the deterministic part at that state is the instruction that returns $\beta$ and halts.

**Proof.** Inspect the instruction at the state. If it were deterministic, its memory-instruction indicator would be false, contradicting the hypothesis that the indicator is true. Thus it is one of the memory instructions. By definition, the deterministic part replaces every memory instruction with the instruction that returns $\beta$ and halts.
