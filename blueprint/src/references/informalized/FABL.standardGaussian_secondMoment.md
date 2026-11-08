<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ContinuousReasonableness.lean :: FABL.standardGaussian_secondMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment of the Standard Gaussian

**Claim.** The second moment of the standard Gaussian measure is $1$: $\int_{\mathbb R}x^2\,d\gamma(x)=1$.

**Proof.** The variance of the identity random variable under a Gaussian with mean $0$ and variance parameter $1$ is $1$ (`variance_fun_id_gaussianReal`). The variance identity expresses this variance as the second moment minus the square of the mean (`variance_eq_integral`). The mean is $0$, so the second moment is $1$.
