<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Preserves Probability

**Claim.** If two predicates agree on every Boolean word of length $m$, then they have equal probabilities under the uniform distribution on such words.

**Proof.** By definition, each probability has the same denominator, $2^m$, and its numerator counts the length-$m$ Boolean strings satisfying the predicate. The hypothesis says that the two predicates select exactly the same strings, so their filtered finite sets have equal cardinality. Their probabilities are therefore equal.
