<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Orthogonality.lean :: BooleanAnalysis.GaussianSpace.integral_hermiteFunction_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multivariate Hermite orthonormality

**Claim.** The product-Gaussian integral of the two multivariate normalized Hermite functions is $1$ when their multi-indices agree and $0$ otherwise.

**Proof.** Express each multivariate Hermite function as the product of its one-coordinate normalized Hermite polynomials (`hermiteFunction_eq_prod`). The product of the two functions is therefore the product over coordinates of the corresponding one-dimensional polynomial products. Independence factors its Gaussian integral into the product of those one-dimensional integrals (`integral_fintype_prod_eq_prod`). By one-dimensional Hermite orthonormality (`integral_normalizedHermite_mul_standardGaussian`), each factor is $1$ when the coordinate indices agree and $0$ otherwise. If the multi-indices agree, every factor is $1$. If they differ, there is a coordinate where they differ, giving a zero factor and hence a zero product.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteFunction_eq_prod`, `BooleanAnalysis.GaussianSpace.integral_normalizedHermite_mul_standardGaussian`.
