<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.multColumn_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Multiplication Column

**Claim.** For every finite bit string $b$ and nonnegative integer $j$, the multiplication column formed from the empty bit string and $b$ is $0$.

**Proof.** The sum defining the column ranges over positions in the empty string. There are no such positions, so the sum is empty and equals $0$.
