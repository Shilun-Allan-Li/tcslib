<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.millsRatio_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for the Mills Ratio

**Claim.** For every $t<0$, the Mills ratio $R(t)=\Phi(t)(-t)/\varphi(t)$ is at most $1$.

**Proof.** The Gaussian density is positive, so multiplying the desired inequality by it preserves the inequality direction. The Gaussian tail bound gives $\Phi(t)\leq\varphi(t)/(-t)$ for $t<0$ (`standardGaussianCDF_le_mills`). Since $-t>0$, multiplying by $-t$ yields $\Phi(t)(-t)\leq\varphi(t)$; division by the positive density gives $R(t)\leq1$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_le_mills`.
