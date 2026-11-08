<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.biasedProb_drop_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Probability of a Fixed-Length Window

**Claim.** When $s+T\le m$, the biased probability that a length-$m$ sample satisfies $B$ on the length-$T$ window after dropping its first $s$ bits equals the biased probability that $B$ holds of a length-$T$ sample.

**Proof.** Write $m=s+T+e$ for some natural number $e$, which exists by the assumed inequality. First apply the prefix-dropping identity (`Randomized.biasedProb_drop`) to remove the first $s$ bits; the remaining sample has length $T+e$, and the event tests its first $T$ bits. Then apply the prefix-taking identity (`Randomized.biasedProb_take`), which says that testing the first $T$ bits of a length-$(T+e)$ sample has the same probability as testing a length-$T$ sample. Associativity of addition aligns the lengths in these two applications.

**Key facts.** `Randomized.biasedProb_drop`, `Randomized.biasedProb_take`.
