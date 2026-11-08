<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MARM.detPart_det -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Instruction Extraction

**Claim.** If the instruction of a memory-augmented register program at a control state is the deterministic instruction $i$, then its deterministic part at that state is $i$, for either Boolean parameter.

**Proof.** The deterministic part returns the instruction itself when the program's instruction at the state is deterministic. Substituting the hypothesis that this instruction is $i$ gives the result; the value of the Boolean parameter is irrelevant in this case.
