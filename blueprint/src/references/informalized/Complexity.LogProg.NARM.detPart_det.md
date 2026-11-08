<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.NARM.detPart_det -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Part at a Deterministic Instruction

**Claim.** If the nondeterministic machine has deterministic instruction $i$ at state $l$, then its deterministic part formed using any Boolean value $\beta$ has instruction $i$ at $l$.

**Proof.** The deterministic part preserves deterministic instructions by definition. Applying that definition to the instruction $i$ at $l$ yields $i$, independently of the chosen Boolean value.
