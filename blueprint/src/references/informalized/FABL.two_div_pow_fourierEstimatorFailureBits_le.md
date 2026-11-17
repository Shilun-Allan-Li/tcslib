<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.two_div_pow_fourierEstimatorFailureBits_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure-Bit Probability Bound

**Claim.** For the specified rational $\delta$, if $k=\lceil\log_2\lceil 2/\delta\rceil\rceil$, then $2/2^k\le\delta$.

**Proof.** By the defining ceiling bound, $2/\delta\le\lceil2/\delta\rceil$. The ceiling is at most $2^k$ by the defining power bound for the base-two ceiling logarithm; hence $2/\delta\le 2^k$. Here $\delta>0$ and $2^k>0$, so clearing denominators yields $2\le\delta 2^k$, which is equivalent to $2/2^k\le\delta$.
