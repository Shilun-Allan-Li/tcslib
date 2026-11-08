<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.gaussianProductDensityDerivative_eq_density_smul_score -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Density Derivative as Density Times Score

**Claim.** For a finite index set $I$, variance parameter $v\ge0$, and $c,z\in\mathbb R^I$, the derivative of the product Gaussian density with respect to its mean is the product density times the linear functional $h\mapsto\sum_{i\in I}((z_i-c_i)/v)h_i$.

**Proof.** Expand the product density in each summand of the derivative. For a fixed coordinate $i$, the product over all coordinates factors as the product over coordinates other than $i$, multiplied by the density in coordinate $i$. Thus the coefficient of the projection onto coordinate $i$ is the full product density times $(z_i-c_i)/v$. Reassembling the finite sum gives the product density multiplied by the sum of the coordinate score functionals.
