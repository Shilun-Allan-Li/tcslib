<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.nastep_det -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic instruction steps agree

**Claim.** When the instruction of the nondeterministic program at $l$ is the deterministic instruction $i$, its one-step transition agrees with that of the deterministic program obtained by replacing choice instructions with $\beta$.

**Proof.** At state $l$, the nondeterministic step follows the deterministic instruction $i$. The deterministic part of the program also assigns $i$ at $l$, by the fact that `detPart` preserves deterministic instructions (`NARM.detPart_det`). Thus both transitions execute the same instruction from the same configuration, with the same oracle and input, and produce the same next configuration.

**Key facts.** `Complexity.LogProg.NARM.detPart_det`.
