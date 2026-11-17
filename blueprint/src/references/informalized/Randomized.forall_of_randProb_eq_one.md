<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.forall_of_randProb_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability one implies universal satisfaction

**Claim.** If a predicate on Boolean strings of length $m$ has probability one under the uniform distribution, then every such string satisfies it.

**Proof.** Suppose, to the contrary, that some string fails the predicate. The probability of failure is the complement of the probability of satisfaction (`randProb_not`), hence is zero. Since the probability is the number of failing strings divided by the positive number $2^m$, a zero probability forces the number of failing strings to be zero. But the assumed counterexample is one such failing string, a contradiction.

**Key facts.** `Randomized.randProb_not`.
