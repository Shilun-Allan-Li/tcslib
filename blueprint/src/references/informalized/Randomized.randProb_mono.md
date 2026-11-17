<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Random-String Probability

**Claim.** If every Boolean word of length $m$ satisfying $A$ also satisfies $B$, then the probability that a uniformly random Boolean word of length $m$ satisfies $A$ is at most the probability that it satisfies $B$.

**Proof.** Among the Boolean words of length $m$, the words satisfying $A$ form a subset of those satisfying $B$, by the assumed implication. Their cardinalities are therefore ordered the same way. Both probabilities divide these counts by the same positive total number $2^m$, so the inequality is preserved.
