<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.gaussianProductDensityHessian_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Formula for the Gaussian Hessian

**Claim.** For finite $I$, $v\ge0$, and $c,z\in\mathbb R^I$, the product Gaussian density Hessian is the sum over $i,j\in I$ of the rank-one forms $(h,k)\mapsto h_jk_i$, with coefficient $\left((z_i-c_i)(z_j-c_j)/v^2-\delta_{ij}/v\right)\prod_{k\in I}p_v(c_k,z_k)$.

**Proof.** Evaluate both sides of the proposed identity on arbitrary vectors $h,k\in\mathbb R^I$. The derivative can be written as the product density times the score, by the density-times-score formula (`gaussianProductDensityDerivative_eq_density_smul_score`). Expanding the resulting sums, the product of the two score terms contributes $(z_i-c_i)(z_j-c_j)/v^2$ to the coefficient of the rank-one form associated with $(i,j)$. The other Hessian term is diagonal: it contributes $-1/v$ when $i=j$ and zero otherwise. Combining these contributions gives the stated coefficient. Since the evaluations agree for every $h,k$, the continuous bilinear forms are equal.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianProductDensityDerivative_eq_density_smul_score`.
