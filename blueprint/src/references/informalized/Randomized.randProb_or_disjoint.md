<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_or_disjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity for Disjoint Events

**Claim.** If no Boolean string of length $m$ satisfies both decidable properties $A$ and $B$, then the probability that a uniformly random Boolean string of length $m$ satisfies at least one of them is the sum of their individual probabilities.

**Proof.** Among the length-$m$ Boolean strings, the strings satisfying $A$ or $B$ form the union of the two corresponding event sets. The hypothesis says these sets are disjoint, so the cardinality of their union is the sum of their cardinalities. Dividing this equality by the common sample-space size $2^m$ gives the sum of the two individual probabilities.
