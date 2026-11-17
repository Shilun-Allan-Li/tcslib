<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.GaussianSpace.tendsto_closedGaussianProfile_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian profile at zero

**Claim.** The closed Gaussian profile tends to zero as its argument approaches zero through positive values.

**Proof.** As $p\to0^+$, the standard Gaussian quantile tends to $-\infty$ (`tendsto_standardGaussianQuantile`). The standard Gaussian density tends to zero at $-\infty$ (`tendsto_standardGaussianPDF_atBot`), so their composition, the Gaussian isoperimetric profile, tends to zero. For positive $p$ sufficiently close to zero we also have $p<1$, and hence the closed profile agrees with the Gaussian isoperimetric profile there (`closedGaussianProfile_eq`). The two functions therefore have the same right-hand limit at zero.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.tendsto_standardGaussianQuantile`, `BooleanAnalysis.ThresholdFunctions.tendsto_standardGaussianPDF_atBot`, `BooleanAnalysis.GaussianSpace.closedGaussianProfile_eq`.
