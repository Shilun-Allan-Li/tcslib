<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.length_le_bnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Code Length Bound

**Claim.** For every Boolean string $y$, its length is at most $(8W+8)(|y|+1)$.

**Proof.** By definition, $bnd(N,y)=(8W+8)(|y|+1)$. Since $|y|\le |y|+1$, we have $|y|\le 1\cdot(|y|+1)$. Also $W$ is a natural number, so $1\le 8W+8$; multiplying this inequality by the nonnegative number $|y|+1$ gives $1\cdot(|y|+1)\le (8W+8)(|y|+1)$. Combining the inequalities proves the claim.
