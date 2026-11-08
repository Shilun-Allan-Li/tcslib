<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.productVariance_le_productTotalInfluence_biased -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Variance and Total Influence

**Claim.** For a function on the sign cube under a product distribution with coordinate bias $0<p<1$, its variance is at most its total product influence.

**Proof.** Use the biased Fourier basis $B$. The Fourier variance formula expresses the variance as the sum of squared Fourier coefficients over all multi-indices except the zero index; the total-influence formula expresses total influence as the sum over all indices of the index order times the squared coefficient. These are the two identities supplied by the variance expansion (FABL.FiniteFourierBasis.variance_eq_sum_sq_fourierCoeff) and the total-influence expansion (FABL.FiniteFourierBasis.productTotalInfluence_eq_sum_order_mul_sq_fourierCoeff). Compare the sums term by term. At the zero index the variance contributes nothing, while the influence contribution is zero because that index has order zero. Every other multi-index has support size at least one, hence order at least one. Its contribution to total influence is therefore at least its squared coefficient, since a square is nonnegative. Summing these termwise inequalities proves the claim.

**Key facts.** `FABL.FiniteFourierBasis.variance_eq_sum_sq_fourierCoeff`, `FABL.FiniteFourierBasis.productTotalInfluence_eq_sum_order_mul_sq_fourierCoeff`.
