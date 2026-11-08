<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementary Event Probability

**Claim.** For any nonnegative integer $m$ and decidable property $A$ of Boolean strings, the probability that a uniformly random Boolean string of length $m$ does not satisfy $A$ is one minus the probability that it satisfies $A$.

**Proof.** Partition the $2^m$ Boolean strings according to whether they satisfy $A$. The two parts are disjoint and exhaust all strings, so their cardinalities sum to $2^m$; the total count is given by `card_univ_bitstrings`. After viewing the counts as rational numbers, rearrange to express the count for the complement as $2^m$ minus the count for $A$. Dividing by $2^m$, which is nonzero, gives the claimed identity: the complement probability is $1$ minus the probability of $A$.

**Key facts.** `Randomized.card_univ_bitstrings`.
