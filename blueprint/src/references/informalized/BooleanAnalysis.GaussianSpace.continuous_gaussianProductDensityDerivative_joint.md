<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.continuous_gaussianProductDensityDerivative_joint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joint Continuity of the Product Density Derivative

**Claim.** For a finite set $I$ and $v\ge0$, the product Gaussian density derivative, as a continuous linear functional on $\mathbb R^I$, is jointly continuous in its mean vector $c$ and input vector $z$.

**Proof.** Expand the derivative into its finite sum of coordinate projections multiplied by scalar coefficients. Each coefficient is assembled from Gaussian densities and the coordinates of $c$ and $z$ using continuous arithmetic operations, including subtraction and division by the fixed variance. Thus each coefficient varies continuously with the pair $(c,z)$. Multiplication by each fixed coordinate projection and finite addition preserve continuity in the operator norm, giving joint continuity.
