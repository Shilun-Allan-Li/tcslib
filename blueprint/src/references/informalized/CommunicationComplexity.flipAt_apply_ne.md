<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean :: CommunicationComplexity.flipAt_apply_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A flip preserves other coordinates

**Claim.** If $j\ne i$, then flipping an input at coordinate $i$ leaves its value at coordinate $j$ unchanged.

**Proof.** The flip changes the input only at coordinate $i$, where its value is replaced by its negation. Since $j$ is different from $i$, the value at $j$ remains the original value.
