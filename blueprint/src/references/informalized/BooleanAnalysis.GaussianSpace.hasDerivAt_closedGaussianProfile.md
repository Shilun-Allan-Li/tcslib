<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_closedGaussianProfile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Gaussian profile

**Claim.** At every $a\in(0,1)$, the closed Gaussian profile is differentiable with derivative equal to the negative lower Gaussian quantile of $a$.

**Proof.** The Gaussian isoperimetric profile has derivative $-\Phi^{-1}(a)$ at every interior point (`hasDerivAt_gaussianIsoperimetric`). Since $(0,1)$ is a neighborhood of $a$, throughout that neighborhood the closed profile agrees with the Gaussian isoperimetric profile (`closedGaussianProfile_eq`). Functions that agree on a neighborhood have the same derivative at its center, so the closed profile has the stated derivative.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_gaussianIsoperimetric`, `BooleanAnalysis.GaussianSpace.closedGaussianProfile_eq`.
