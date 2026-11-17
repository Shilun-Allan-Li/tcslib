<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/NormalizedSums.lean :: BooleanAnalysis.GaussianSpace.normalizedSum_lipschitz_comparison -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian comparison for normalized sums

**Claim.** There is a positive constant $K$ such that, for every positive integer $n$, every independent family satisfying the stated invariance moment conditions, and every $c$-Lipschitz function, the difference between the expectation of the function of the normalized sum and its standard Gaussian expectation is at most $Kc n^{-1/4}$.

**Proof.** 1. Apply the invariance principle for multilinear polynomials (`invariance_lipschitz`) to the normalized-sum polynomial, comparing the given independent variables with independent standard Gaussian coordinates. The polynomial has degree at most one (`normalizedSumPolynomial_hasDegreeAtMost`), its cube variance is one (`cubeVariance_normalizedSumPolynomial`), and each coordinate influence is $1/n$ (`influence_normalizedSumPolynomial`). Thus the hypotheses of the invariance principle hold with variance bound one and influence parameter $1/n$. It bounds the difference of the two Lipschitz expectations by its universal constant times $c(1/n)^{1/4}$.

2. The polynomial evaluated on the original variables is their sum divided by $\sqrt n$ (`evalMultilinearRV_normalizedSumPolynomial`). For the Gaussian comparison, take the product measure of $n$ standard Gaussian laws. Each coordinate has the required invariance moments (`hasInvarianceMoments_gaussianCoordinate`), and these coordinates are independent under the product measure. The sum divided by $\sqrt n$ has the standard Gaussian law: this is the Gaussian projection fact (`measurePreserving_gaussianProjection`), since the squared coefficients sum to one. Consequently its Lipschitz expectation is exactly the standard Gaussian expectation.

3. The comparison principle gives a bound with the factor $K(1/n)^{1/4}c$. Choosing twice its constant still gives a positive universal constant and yields the stated form after the elementary rearrangement of factors.

**Key facts.** `BooleanAnalysis.GaussianSpace.invariance_lipschitz`, `BooleanAnalysis.GaussianSpace.normalizedSumPolynomial_hasDegreeAtMost`, `BooleanAnalysis.GaussianSpace.cubeVariance_normalizedSumPolynomial`, `BooleanAnalysis.GaussianSpace.influence_normalizedSumPolynomial`, `BooleanAnalysis.GaussianSpace.evalMultilinearRV_normalizedSumPolynomial`, `BooleanAnalysis.GaussianSpace.hasInvarianceMoments_gaussianCoordinate`, `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianProjection`.
