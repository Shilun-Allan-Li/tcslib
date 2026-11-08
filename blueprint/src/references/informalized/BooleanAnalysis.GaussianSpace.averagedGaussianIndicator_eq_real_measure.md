<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_eq_real_measure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Averaged Indicator as Gaussian Measure

**Claim.** For measurable $A\subseteq\mathbb R^n$, the averaged indicator at $\theta,x$ equals the standard Gaussian measure of the set of vectors $y$ for which $\cos(\theta)x+\sin(\theta)y$ belongs to $A$.

**Proof.** The map $y\mapsto\cos(\theta)x+\sin(\theta)y$ is measurable, so the preimage of $A$ is measurable. The integrand defining the averaged indicator is exactly the indicator function of this preimage. Integrating an indicator gives the measure of its set, which proves the identity.
