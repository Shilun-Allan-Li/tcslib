<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.productInner_eq_projection_add_laplacian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate projection decomposition

**Claim.** The product inner product of $f$ and $g$ is the sum of the inner product of their coordinate projections and the inner product of their coordinate Laplacians.

**Proof.** Apply Plancherel to each of the three inner products, so the desired identity becomes an equality of sums of products of Fourier coefficients. At a multi-index whose $i$th entry is the constant index, the projection retains the coefficient and the Laplacian coefficient vanishes. At every other multi-index, the projection coefficient vanishes and the Laplacian retains the coefficient. Thus, term by term, the product of the two original coefficients is exactly the sum of the products contributed by the projection and by the Laplacian. Summing over all multi-indices proves the identity.

**Key facts.** `FABL.FiniteFourierBasis.plancherel`, `FABL.FiniteFourierBasis.fourierCoeff_coordinateProjection`, `FABL.FiniteFourierBasis.fourierCoeff_productCoordinateLaplacian`.
