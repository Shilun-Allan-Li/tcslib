<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.measurable_averagedGaussianIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of the Gaussian Indicator Average

**Claim.** For a measurable set $A$ and fixed $\theta$, the Gaussian average of its indicator after rotation is measurable as a function of the input vector.

**Proof.** Consider the integrand jointly in the input vector $x$ and the integration variable $y$. The map $(x,y)\mapsto \cos(\theta)x+\sin(\theta)y$ is measurable, so composing it with the indicator of the measurable set $A$ gives a jointly measurable function. This function is strongly measurable. The theorem on integrating a strongly measurable function over the right factor of a product measure then implies that its integral in $y$ is measurable in $x$. The standard Gaussian measure is a probability measure, as needed for this product-integral result.
