<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.GaussianSpace.closedGaussianProfile_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Gaussian profile

**Claim.** The closed Gaussian profile is nonnegative at every real input.

**Proof.** By definition, the profile is the Gaussian isoperimetric profile when the input lies in $(0,1)$ and is zero otherwise. In the first case the standard Gaussian density is positive at the corresponding quantile (`BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`), so the profile is nonnegative; in the second case it is zero.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
