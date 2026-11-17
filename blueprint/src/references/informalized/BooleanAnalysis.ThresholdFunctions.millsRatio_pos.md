<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.millsRatio_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Mills Ratio

**Claim.** For every real $t<0$, the Mills ratio $R(t)=\Phi(t)(-t)/\varphi(t)$ is positive.

**Proof.** The Gaussian cumulative distribution function is positive, and $-t>0$ because $t<0$. Their product is therefore positive. The standard Gaussian density is also positive, so dividing that product by the density preserves positivity (`standardGaussianCDF_pos` and `standardGaussianPDF_pos`).

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
