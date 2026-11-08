<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability After Dropping a Prefix

**Claim.** For any natural numbers $S,n$ and predicate $P$ on Boolean words, the probability that the suffix after the first $S$ bits of a uniformly random word of length $S+n$ satisfies $P$ equals the probability that a uniformly random word of length $n$ satisfies $P$.

**Proof.** For each word, the condition on its suffix is unchanged if we also require its length-$S$ prefix to satisfy the constantly true predicate. The probability of the resulting conjunction factors into the probability of that prefix condition times the probability that the length-$n$ suffix satisfies $P$, by the split rule for independent blocks (`Randomized.randProb_split`). The first factor is $1$ (`Randomized.randProb_true`), giving the desired equality.

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_split`, `Randomized.randProb_true`.
