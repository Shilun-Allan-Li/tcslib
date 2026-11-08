<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_step_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on one search round

**Claim.** If $|s|\le |w|+1$, then the word produced by one search round has length at most $|w|+1$.

**Proof.** If $|s|\le |w|$, the round appends one bit, so its new length is $|s|+1\le |w|+1$. Otherwise the round leaves $s$ unchanged, and the assumed bound $|s|\le |w|+1$ gives the result directly.
