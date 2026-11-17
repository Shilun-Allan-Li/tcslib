<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/SubGaussian.lean :: integral_pow_four_le_of_subgaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth moment bound

**Claim.** Under the stated sub-Gaussian moment-generating-function bound and second-moment identity, $Z^4$ is integrable and its expectation is at most $4\sigma^4$.

**Proof.** Choose $t_0=1/(8\sigma^2)$. The exponential-square estimate (`integral_exp_mul_sq_le_of_subgaussian`) applies because $2\sigma^2t_0=1/4<1$, and it bounds $\mathbb E e^{t_0Z^2}$ by $231/200$. For every outcome, the quadratic Taylor lower bound for the exponential gives $1+t_0Z^2+t_0^2Z^4/2\le e^{t_0Z^2}$. In particular, this inequality bounds $Z^4$ by a constant multiple of the integrable function $e^{t_0Z^2}$, so $Z^4$ is integrable. The second-moment identity also ensures that $Z^2$ is integrable: otherwise its integral would be infinite, contrary to the given finite value. We may now integrate the pointwise inequality. Using the probability-space normalization and $\mathbb E Z^2=\sigma^2$, its left side becomes $1+t_0\sigma^2+(t_0^2/2)\mathbb E Z^4$. Comparing with $231/200$ and substituting $t_0\sigma^2=1/8$ yields $t_0^2\mathbb E Z^4\le3/50$. Since $t_0^2=1/(64\sigma^4)$, this gives $\mathbb E Z^4\le(96/50)\sigma^4\le4\sigma^4$.

**Key facts.** `integral_exp_mul_sq_le_of_subgaussian`.
