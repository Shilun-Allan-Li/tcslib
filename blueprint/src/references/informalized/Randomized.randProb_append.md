<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability Under Concatenation

**Claim.** For properties of Boolean strings, the probability of $A$ on strings of length $b+m$ is the average, over all length-$b$ prefixes, of the probability that the concatenated string satisfies $A$.

**Proof.** Identify each Boolean string of length $b+m$ with its unique pair consisting of a length-$b$ prefix and a length-$m$ suffix. Under this bijection, the strings satisfying $A$ are counted by first fixing the prefix $u$ and then counting the suffixes $l$ for which $u\mathbin{++}l$ satisfies $A$. Summing these counts over all prefixes gives the total count. Dividing by the total number $2^{b+m}=2^b2^m$ of strings yields the stated average, with each suffix count normalized as its length-$m$ probability.
