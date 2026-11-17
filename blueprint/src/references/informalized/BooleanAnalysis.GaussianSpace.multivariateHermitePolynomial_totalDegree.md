<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Degree.lean :: BooleanAnalysis.GaussianSpace.multivariateHermitePolynomial_totalDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Degree of a Multivariate Hermite Polynomial

**Claim.** The total degree of the product of normalized Hermite polynomials associated to a multi-index $\alpha$ equals $\sum_i\alpha_i$.

**Proof.** Write each factor as the multivariate polynomial obtained by embedding the univariate normalized Hermite polynomial of degree $\alpha_i$ in coordinate $i$. Every factor is nonzero (BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_ne_zero), so the total degree of their product is the sum of their total degrees (BooleanAnalysis.GaussianSpace.totalDegree_finset_prod_of_ne_zero). Embedding a univariate polynomial into one variable preserves its degree as total degree (BooleanAnalysis.GaussianSpace.totalDegree_toMvPolynomial), and the normalized Hermite polynomial has degree $\alpha_i$ (BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_natDegree). Summing these degrees gives the asserted formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.totalDegree_finset_prod_of_ne_zero`, `BooleanAnalysis.GaussianSpace.totalDegree_toMvPolynomial`, `BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_natDegree`, `BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_ne_zero`.
