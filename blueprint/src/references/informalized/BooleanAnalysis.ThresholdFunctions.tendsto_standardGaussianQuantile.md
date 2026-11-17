<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_standardGaussianQuantile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Quantile Divergence

**Claim.** As $\alpha$ tends to $0$ through positive values, the standard Gaussian quantile tends to negative infinity.

**Proof.** To show divergence to negative infinity, fix any real threshold $M$. The Gaussian cumulative distribution function is positive at $M$, so $\min(\Phi(M),1)>0$. For every sufficiently small positive $\alpha$, we have $\alpha<\min(\Phi(M),1)$, hence $0<\alpha<1$ and $\alpha<\Phi(M)$. The quantile identity gives $\Phi(Q(\alpha))=\alpha$, so $\Phi(Q(\alpha))<\Phi(M)$. Since the Gaussian cumulative distribution function is strictly increasing (`standardGaussianCDF_strictMono`), this implies $Q(\alpha)<M$. As this holds for every $M$, the quantile tends to negative infinity.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_quantile`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_strictMono`.
