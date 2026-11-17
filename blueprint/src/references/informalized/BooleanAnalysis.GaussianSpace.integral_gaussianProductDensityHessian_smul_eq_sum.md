<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.integral_gaussianProductDensityHessian_smul_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Hessian integral identity

**Claim.** The Lebesgue integral of the bounded measurable function times the Gaussian product density Hessian is the sum of the coordinate bilinear forms weighted by the corresponding Gaussian Hessian score expectations.

**Proof.** Let $\mu$ be the product Gaussian law, let $T_{ij}(h,k)=h_jk_i$, and let $K_{ij}(z)$ be the scalar second score $((z_i-c_i)(z_j-c_j)/v^2-\mathbf 1_{i=j}/v)f(z)$. The Hessian expansion (`gaussianProductDensityHessian_eq_sum`) expresses the integrand as the product density times the finite double sum $\sum_{i,j}K_{ij}(z)T_{ij}$. Distributing that density across the sum gives the first displayed integral. The product-Gaussian density conversion formula (`integral_pi_gaussianReal_eq_integral_smul`) turns it into the $\mu$-integral of the double sum. Each scalar $K_{ij}$ is integrable by the product-Hessian integrability bound (`integrable_productHessian_mul`), and hence so is its fixed bilinear-form multiple. Finite-sum linearity, first over $i$ and then over $j$, moves the sums outside the integral; linearity for fixed bilinear forms yields exactly the stated coefficients.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianProductDensityHessian_eq_sum`, `BooleanAnalysis.GaussianSpace.integral_pi_gaussianReal_eq_integral_smul`, `BooleanAnalysis.GaussianSpace.integrable_productHessian_mul`.
