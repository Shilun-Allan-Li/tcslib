<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.integral_gaussianProductDensityDerivative_smul_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian score integral identity

**Claim.** The Lebesgue integral of the bounded measurable function times the Gaussian product density derivative equals the sum of coordinate projections weighted by the corresponding Gaussian score expectations.

**Proof.** Write $\mu$ for the product law of the independent coordinates, and let $S(z)$ be the sum over $i$ of $((z_i-c_i)/v)f(z)$ times the $i$th coordinate projection. The product density derivative identity ( `gaussianProductDensityDerivative_eq_density_smul_score`) rewrites the integrand as the product Gaussian density times $S(z)$; distributing the density across the finite sum gives the first integral in this form. The product-Gaussian density conversion formula (`integral_pi_gaussianReal_eq_integral_smul`) then identifies this Lebesgue integral with $\int S\,d\mu$. Each summand of $S$ is integrable: the coordinate score integrability bound (`gaussianCoordinate_first_kernel_integrable_bound`) gives integrability of its scalar coefficient, which remains integrable after multiplication by the fixed coordinate projection. Thus finite-sum linearity moves the sum outside the integral, and linearity for a fixed vector-valued factor gives the claimed coefficient expectations.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianProductDensityDerivative_eq_density_smul_score`, `BooleanAnalysis.GaussianSpace.integral_pi_gaussianReal_eq_integral_smul`, `BooleanAnalysis.GaussianSpace.gaussianCoordinate_first_kernel_integrable_bound`.
