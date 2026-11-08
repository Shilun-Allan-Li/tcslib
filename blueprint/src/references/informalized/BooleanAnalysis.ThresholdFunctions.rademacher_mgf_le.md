<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/DegreeOne.lean :: BooleanAnalysis.ThresholdFunctions.rademacher_mgf_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moment Bound for a Rademacher Sum

**Claim.** If the coefficients satisfy $\sum_i a_i^2=1$, then for every real $t$, the uniform Boolean expectation of $\exp(t\sum_i a_i\sigma(X_i))$ is at most $\exp(t^2/2)$.

**Proof.** First factor the expectation across coordinates. The exponential of the sum is the product of the coordinate exponentials, and the uniform average over all Boolean vectors factors into the product of the one-coordinate averages. Each such average is $\cosh(t a_i)$, so the expectation equals $\prod_i\cosh(t a_i)$. The standard inequality $\cosh u\leq e^{u^2/2}$ bounds this product by $\prod_i e^{(t a_i)^2/2}=e^{(t^2/2)\sum_i a_i^2}$. The normalization of the coefficients makes the last expression $e^{t^2/2}$, proving the claim.
