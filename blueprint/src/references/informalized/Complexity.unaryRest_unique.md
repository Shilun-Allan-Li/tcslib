<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPath.lean :: Complexity.unaryRest_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Unary Rest Length

**Claim.** If a word satisfies the unary-rest condition at lengths $n$ and $n'$, then $n=n'$.

**Proof.** Suppose the lengths differ. Natural-number order then gives either $n<n'$ or $n'<n$. In the first case, the condition for length $n'$ says that the pair at positions $2n,2n+1$ consists of two ones, because $n<n'$. But the condition for length $n$ says that the bit at position $2n$ is zero, a contradiction. In the second case, the same argument with the two lengths exchanged gives a contradiction. Therefore the lengths are equal.
