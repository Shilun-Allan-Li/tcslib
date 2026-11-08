<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InputMoments.lean :: BooleanAnalysis.GaussianSpace.integral_second_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Gaussian Second Moment

**Claim.** The second moment of the standard Gaussian measure on $\mathbb R$ is one.

**Proof.** The variance of the identity random variable under a Gaussian law with mean zero and variance parameter one is one (`variance_fun_id_gaussianReal`). The variance identity expresses this variance as the integral of the squared deviation from the mean. Since the mean is zero, that squared deviation is $x^2$, so the desired integral equals one.
