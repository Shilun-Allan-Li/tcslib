<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteFourierBasis.productVariance_le_productTotalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance–influence inequality

**Claim.** For every function on the product space, its variance is at most its total influence.

**Proof.** By the Fourier variance identity, the variance is the sum of squared Fourier coefficients over all multi-indices except the zero multi-index. By the total-influence identity, total influence is the sum over all multi-indices of the squared coefficient weighted by the order of that multi-index. Compare these sums term by term. At the zero multi-index, the variance contributes nothing, and the influence weight is also zero because its support is empty. At every other multi-index, the support is nonempty, so its order, the size of that support, is at least one. Its weighted square therefore dominates its unweighted square, proving the inequality after summation.

**Key facts.** `FABL.FiniteFourierBasis.variance_eq_sum_sq_fourierCoeff`, `FABL.FiniteFourierBasis.productTotalInfluence_eq_sum_order_mul_sq_fourierCoeff`.
