<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.NARM.detPart_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Part at a Choice

**Claim.** If the nondeterministic machine chooses between $l_1$ and $l_0$ at state $l$, then its deterministic part formed using any Boolean value $\beta$ returns $\beta$ and halts at $l$.

**Proof.** By definition, the deterministic part preserves deterministic instructions and replaces a choice instruction with the return instruction carrying $\beta$. Since the instruction at $l$ is the stated choice, its deterministic part at $l$ is exactly that return instruction.
