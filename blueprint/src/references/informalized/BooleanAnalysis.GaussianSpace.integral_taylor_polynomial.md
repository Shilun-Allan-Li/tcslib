<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Taylor.lean :: BooleanAnalysis.GaussianSpace.integral_taylor_polynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integration of a Taylor Polynomial

**Claim.** For a random variable with finite $p$th moment on a probability space, integrating the Taylor polynomial of degree less than $m$, where $m\le p$, gives the sum of its Taylor coefficients times the corresponding moments of the random variable.

**Proof.** First distribute $(bX)^j$ as $b^jX^j$ in each term. The finite sum can be integrated term by term. To justify this, for each $j<m\le p$, the $j$th power of $X$ is integrable: the finite-moment product lemma (`integrable_mul_pow_of_memLp`) applied to two copies of $X$, with exponents $j$ and $0$, supplies this integrability. Each Taylor coefficient and $b^j$ are constants, so the integral of each term is its constant factor times $\int X^j\,d\mu$. Summing these identities gives the formula.

**Key facts.** `BooleanAnalysis.Hypercontractivity.integrable_mul_pow_of_memLp`.
