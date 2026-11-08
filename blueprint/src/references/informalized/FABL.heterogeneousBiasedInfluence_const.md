<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.heterogeneousBiasedInfluence_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Under Constant Bias

**Claim.** When every coordinate has bias $p$, the heterogeneous expected conditional variance at coordinate $i$ equals the product-measure influence at that coordinate for the common biased sign distribution.

**Proof.** Use the biased Fourier basis associated with $p$. Its product-influence identity says that the product influence equals the product mean of the coordinate conditional variance. With constant bias, the heterogeneous product distribution and the product distribution of the common biased sign law are the same, so this expected conditional variance is precisely the heterogeneous influence in the claim.

**Key facts.** `FABL.FiniteFourierBasis.productInfluence_eq_expect_coordinateConditionalVariance`.
