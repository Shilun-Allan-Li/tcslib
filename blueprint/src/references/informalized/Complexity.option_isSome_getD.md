<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableauCorrect.lean :: Complexity.option_isSome_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of an optional Boolean

**Claim.** For every optional Boolean value $o$, the construction that returns its default-false value when present and no value when absent gives back $o$.

**Proof.** There are two cases. If $o$ is absent, its presence test is false, and the construction returns no value. If $o$ contains a Boolean $b$, its presence test is true and its default-false value is $b$, so the construction returns that same optional value.
