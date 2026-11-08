<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_quantile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Quantile Recovery

**Claim.** For every $0<\alpha<1$, the standard Gaussian CDF evaluated at its lower $\alpha$-quantile equals $\alpha$.

**Proof.** The standard Gaussian CDF takes the value $\alpha$ at some real $t$ (`exists_standardGaussianCDF_eq`). The quantile characterization for any such point says that the lower $\alpha$-quantile is exactly $t$ (`standardGaussianQuantile_eq`). Substituting this equality into $\Phi(t)=\alpha$ gives the result.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.exists_standardGaussianCDF_eq`, `BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_eq`.
