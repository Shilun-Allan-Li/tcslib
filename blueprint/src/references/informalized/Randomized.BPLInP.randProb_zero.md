<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPCount.lean :: Randomized.BPLInP.randProb_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability with No Coins

**Claim.** For every decidable predicate $A$ on bit strings, the probability that $A$ holds on a uniformly random string of length zero is $1$ if it holds on the empty string, and $0$ otherwise.

**Proof.** There is exactly one function from the zero-element set of coin positions to the Boolean alphabet, and its associated bit string is empty. Thus the set of length-zero coin outcomes satisfying $A$ has cardinality one when $A$ holds on the empty string, and cardinality zero otherwise. The denominator $2^0$ is one, so the probability is respectively $1$ or $0.
