<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCounts_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Round Advances the Counts

**Claim.** If $b$ correctly marks the input-head boundary status at time $t$, advancing the counts using the machine’s displacements computed with $b$ gives the count vector at time $t+1$.

**Proof.** The correct-tag condition ensures that the machine’s displacement vector computed using $b$ is the same as the one computed using the tag derived directly from the configuration (`Complexity.clMoves_tag`). Substituting that equality into the proposed advance leaves exactly the recursive definition of the count vector at time $t+1}.

**Key facts.** `Complexity.clMoves_tag`.
