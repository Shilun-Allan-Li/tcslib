<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.continuous_gaussianProductDensityDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Product Density Derivative

**Claim.** For a finite set $I$, $v\ge0$, and fixed $c\in\mathbb R^I$, the product Gaussian density derivative at mean $c$ and input $z$, as a continuous linear functional on $\mathbb R^I$, is continuous in operator norm as a function of $z$.

**Proof.** Expand the derivative as a finite sum of scalar coefficients times coordinate projections. Each coefficient is built from Gaussian densities, coordinate evaluations, subtraction, division by the fixed variance, and finite products. These operations preserve continuity in $z$, and each coordinate projection is a fixed continuous linear functional. Scalar multiplication and finite addition in the space of continuous linear functionals preserve continuity, proving the claim.
