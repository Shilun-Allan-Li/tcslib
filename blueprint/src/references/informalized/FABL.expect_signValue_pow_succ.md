<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.expect_signValue_pow_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moment of a Uniform Random Sign

**Claim.** For a uniform sign $b$ and nonnegative integer $k$, the mean of $b^{k+1}$ is $1$ if $k$ is odd and $0$ if $k$ is even.

**Proof.** Split into the two parity cases. If $k$ is odd, then $k+1$ is even, so both possible signs have $(k+1)$st power $1$; the mean of this constant function is $1$. If $k$ is even, then $k+1$ is odd, so $b^{k+1}=b$ for each sign. Its mean is zero by the fact that the two sign values cancel (`expect_signValue_eq_zero`).

**Key facts.** `FABL.expect_signValue_eq_zero`.
