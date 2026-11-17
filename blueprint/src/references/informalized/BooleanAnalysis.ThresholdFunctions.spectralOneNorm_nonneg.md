<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.spectralOneNorm_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative spectral one-norm

**Claim.** For every real-valued function on the Boolean cube, the sum of the absolute values of its Fourier–Walsh coefficients is nonnegative.

**Proof.** Each absolute value $|\widehat f(S)|$ is nonnegative. A finite sum of nonnegative terms is nonnegative, so the spectral one-norm is nonnegative.
