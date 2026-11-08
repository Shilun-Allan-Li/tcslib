<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.astep_mdetPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Step Independence

**Claim.** For an instruction that is deterministic at state $l$, the arithmetic-machine step from that state is the same for either choice of the halt answer.

**Proof.** Since $A(l)$ is the deterministic instruction $i$, both deterministic parts return $i$ at $l$ (the fact that a deterministic instruction ignores the halt answer, `MARM.detPart_det`). Applying the step definition to the same instruction, oracle, input, registers, and result therefore gives identical configurations.

**Key facts.** `Complexity.LogProg.MARM.detPart_det`.
