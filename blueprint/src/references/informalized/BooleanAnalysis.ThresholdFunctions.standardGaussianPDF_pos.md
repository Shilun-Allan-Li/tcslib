<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Gaussian Density

**Claim.** For every real number $x$, the standard Gaussian density satisfies $0<\varphi(x)$.

**Proof.** The standard Gaussian density is the real Gaussian density with mean $0$ and variance $1$. The Gaussian density positivity theorem applies for every real argument when the variance is nonzero; here the variance is $1$, so it is nonzero. Hence $\varphi(x)>0$.
