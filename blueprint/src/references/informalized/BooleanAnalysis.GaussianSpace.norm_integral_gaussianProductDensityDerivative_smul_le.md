<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.norm_integral_gaussianProductDensityDerivative_smul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrated Gaussian derivative bound

**Claim.** For measurable $f$ with $|f(z)|\leq1$, the norm of its integral against the product Gaussian density derivative is at most $|I|(1+1/v)$.

**Proof.** First express the vector-valued integral as a sum over coordinates: its $i$th term is the scalar integral of $(z_i-c_i)f(z)/v$ against the product Gaussian probability measure, multiplied by the $i$th coordinate projection. This identity is the integral expansion for the product density derivative (`integral_gaussianProductDensityDerivative_smul_eq_sum`). Each coordinate projection has operator norm at most $1$ (`norm_coordinateProjection_le_one`). The absolute value of the corresponding scalar integral is at most $1+1/v$, by the integrability and first-kernel estimate (`gaussianCoordinate_first_kernel_integrable_bound`). Thus each summand has norm at most $1+1/v$. The triangle inequality bounds the norm of the sum by the sum of these bounds, which has $|I|$ equal terms.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_gaussianProductDensityDerivative_smul_eq_sum`, `BooleanAnalysis.GaussianSpace.norm_coordinateProjection_le_one`, `BooleanAnalysis.GaussianSpace.gaussianCoordinate_first_kernel_integrable_bound`.
