<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.biasedProb_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Formula for Biased Probability

**Claim.** For any real $\rho$, nonnegative integer $m$, and predicate $A$, the biased probability on strings of length $m+1$ is $\rho$ times the probability for the predicate obtained by prefixing true, plus $1-\rho$ times the probability for the predicate obtained by prefixing false, both on strings of length $m$.

**Proof.** Unfold the recursive definition of biased probability at length $m+1$. Its defining clause is exactly the stated decomposition into the true and false first-bit branches.
