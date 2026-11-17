<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productCovariance_eq_projection_covariance_add_laplacian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Covariance decomposition by coordinate

**Claim.** The covariance of $f$ and $g$ is the covariance of their coordinate projections plus the product inner product of their coordinate Laplacians.

**Proof.** Expand the covariance in the Fourier basis: it is the sum, over all nonconstant multi-indices, of the products of the corresponding coefficients (`FiniteFourierBasis.covariance_eq_sum_fourierCoeff_mul`). Parseval's identity expresses the inner product of the coordinate Laplacians as the sum of the products of their coefficients over all multi-indices (`FiniteFourierBasis.plancherel`). The coefficient of a coordinate projection agrees with the original coefficient precisely when that coordinate's index is the distinguished constant index, and is zero otherwise (`FiniteFourierBasis.fourierCoeff_coordinateProjection`). For the coordinate Laplacian the complementary rule holds: it retains the coefficient when the coordinate index is nonconstant and vanishes when it is constant (`FiniteFourierBasis.fourierCoeff_productCoordinateLaplacian`). Thus the projection covariance collects exactly the nonconstant global indices that are constant in coordinate $j$, while the Laplacian inner product collects those nonconstant in coordinate $j$. These two disjoint cases partition all nonconstant multi-indices, so their sums add to the full covariance.

**Key facts.** `FABL.FiniteFourierBasis.covariance_eq_sum_fourierCoeff_mul`, `FABL.FiniteFourierBasis.plancherel`, `FABL.FiniteFourierBasis.fourierCoeff_coordinateProjection`, `FABL.FiniteFourierBasis.fourierCoeff_productCoordinateLaplacian`.
