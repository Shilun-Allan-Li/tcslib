<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.multRows_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Sum of Rows

**Claim.** For finite bit strings $a,b$ and nonnegative integers $j,p$, the sum of the row sums over positions in $a$ is at most the length of $a$.

**Proof.** Each row in the sum is at most $1$ by the row bound (`Complexity.multRow_le_one`). Thus the sum is at most the sum of $1$ over the positions in $a$, which equals the length of $a$.

**Key facts.** `Complexity.multRow_le_one`.
