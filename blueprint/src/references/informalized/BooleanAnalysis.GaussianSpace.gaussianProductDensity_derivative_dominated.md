<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.gaussianProductDensity_derivative_dominated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Common Envelope for Density and Derivative

**Claim.** For finite $I$, nonzero variance parameter $v\ge0$, and $M\ge0$, there is a nonnegative Lebesgue-integrable function of $z$ that uniformly bounds both the absolute product Gaussian density and the operator norm of its mean derivative whenever $|m_i|\le M$ for every coordinate.

**Proof.** Use the one-dimensional domination theorem (`gaussianPDFReal_two_derivatives_dominated`) to choose a nonnegative integrable envelope $a$ bounding each coordinate density and its first-derivative factor for all allowed means. Its coordinatewise product is integrable under product Lebesgue measure. The product density is nonnegative and bounded by $\prod_j a(z_j)$, so it is bounded by $(|I|+1)\prod_j a(z_j)$. For each summand of the mean derivative, the norm of the coordinate projection is at most one (`norm_coordinateProjection_le_one`). The absolute coefficient of that summand is bounded by $\prod_j a(z_j)$: apply the density envelope in every coordinate other than its index and the first-derivative envelope at that index. The triangle inequality then bounds the derivative norm by $|I|\prod_j a(z_j)$. Consequently, $(|I|+1)\prod_j a(z_j)$ is a common nonnegative integrable envelope.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianPDFReal_two_derivatives_dominated`, `BooleanAnalysis.GaussianSpace.norm_coordinateProjection_le_one`.
