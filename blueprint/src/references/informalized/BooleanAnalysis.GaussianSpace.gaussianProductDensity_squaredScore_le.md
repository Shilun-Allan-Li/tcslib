<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.gaussianProductDensity_squaredScore_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound for a Squared Gaussian Score

**Claim.** Under the stated coordinatewise envelope bounds, for every $i\in I$ the squared score contribution times the product Gaussian density is at most $(1+1/v)\prod_{j\in I}a_j$.

**Proof.** First isolate coordinate $i$. The identity $\frac{(z_i-c_i)^2}{v^2}p_v(c_i,z_i)=\left(\frac{(z_i-c_i)^2}{v^2}-\frac1v\right)p_v(c_i,z_i)+\frac1v p_v(c_i,z_i)$ and the triangle inequality bound this by $a_i+(1/v)a_i=(1+1/v)a_i$, using the assumed second-derivative and density bounds. The remaining coordinates contribute a product bounded by $\prod_{j\ne i}a_j$, since each density is nonnegative and at most $a_j$. Multiplying the two bounds and restoring the $i$th factor gives $(1+1/v)\prod_j a_j$.
