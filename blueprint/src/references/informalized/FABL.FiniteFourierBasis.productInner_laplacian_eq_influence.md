<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.productInner_laplacian_eq_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner product with the coordinate Laplacian

**Claim.** The inner product of $f$ with its coordinate Laplacian equals the influence of $f$ at that coordinate.

**Proof.** By Plancherel, the inner product is the sum, over all multi-indices, of the product of the corresponding Fourier coefficients of $f$ and its coordinate Laplacian. The Laplacian coefficient is zero when the coordinate index is the constant index, and otherwise equals the coefficient of $f$. Consequently, the sum reduces to the squared coefficients over indices with nonconstant coordinate entry. The Fourier formula for influence is precisely this sum.

**Key facts.** `FABL.FiniteFourierBasis.plancherel`, `FABL.FiniteFourierBasis.fourierCoeff_productCoordinateLaplacian`, `FABL.FiniteFourierBasis.productInfluence_eq_sum_sq_fourierCoeff`.
