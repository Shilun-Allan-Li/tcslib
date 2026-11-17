<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_standardGaussianPDF_atBot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Density Decay

**Claim.** The standard Gaussian density tends to $0$ as its argument tends to negative infinity.

**Proof.** By the Gaussian density formula (`standardGaussianPDF_eq`), the density is a positive constant times $\exp(-x^2/2)$. Since $x^2\to+\infty$ as $x\to-\infty$ (`tendsto_sq_atBot`), we have $-x^2/2\to-\infty$. The exponential tends to $0$ at negative infinity, and multiplying by the fixed constant preserves this limit.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq`, `BooleanAnalysis.ThresholdFunctions.tendsto_sq_atBot`.
