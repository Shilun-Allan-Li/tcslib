<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.expect_abs_le_sqrt_expect_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First moment bounded by the second

**Claim.** For a real-valued function on the uniformly distributed sign cube, its expected absolute value is at most the square root of its expected square.

**Proof.** Apply the finite Cauchy–Schwarz inequality to the functions $|q|$ and $1$. Since the expectation of $1$ is $1$, and $|q|^2=q^2$, this gives $(\mathbb{E}|q|)^2\leq\mathbb{E}q^2$. Both expectations are nonnegative, because their integrands are nonnegative. Taking nonnegative square roots yields the asserted inequality.
