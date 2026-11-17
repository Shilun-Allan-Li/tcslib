<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.continuous_gaussianProductDensityHessian_joint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joint Continuity of the Product Density Hessian

**Claim.** For a finite set $I$ and $v\ge0$, the product Gaussian density Hessian, viewed as a continuous bilinear form on $\mathbb R^I$, is jointly continuous in its mean vector $c$ and input vector $z$.

**Proof.** Use the identity `gaussianProductDensityHessian_eq_sum` to express the Hessian as a finite double sum of scalar coefficients times fixed bilinear forms formed from coordinate projections. Each coefficient is made from the coordinates of $c$ and $z$, Gaussian densities, finite products, and continuous arithmetic operations, so it is continuous in $(c,z)$. Scalar multiplication by the fixed bilinear forms and finite summation preserve continuity in the normed space of bilinear forms. Hence the Hessian depends continuously on $(c,z)$.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianProductDensityHessian_eq_sum`.
