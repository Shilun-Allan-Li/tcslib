<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix.lean :: Complexity.KarpLipton.mem_prefixLangOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a Prefix Language

**Claim.** A bit string belongs to the prefix language determined by $\ell$ exactly when there is a suffix $s$ such that the marker-dropped second projection, followed by $s$, has length $\ell$ of the first projection and its encoding with that first projection belongs to $V$.

**Proof.** By definition, the prefix language consists exactly of the strings for which a suffix $s$ satisfies these two conditions. Hence the membership statement and the existential characterization are the same proposition.
