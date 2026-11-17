<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean :: Complexity.Codec.bnd_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Encoding Bound

**Claim.** If $s\le 2|y|$, then the stated configuration-window length is at most $b(y)=(8W+8)(|y|+1)$.

**Proof.** From $s\le 2|y|$ we get $2s+1\le 4|y|+1$. Since $2W$ is nonnegative, multiplying gives $2W(2s+1)\le 2W(4|y|+1)=8W|y|+2W$. Expanding the definition of $b(y)$ gives $8W|y|+8W+8|y|+8$. The desired inequality now follows by comparing these expressions and accounting for the remaining terms $|y|+2(|y|+1)+4$.
