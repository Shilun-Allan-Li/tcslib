<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_mem_unitInterval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of the Averaged Indicator

**Claim.** For measurable $A\subseteq\mathbb R^n$, the averaged indicator at any $\theta$ and $x$ lies between zero and one.

**Proof.** By the identity expressing the averaged indicator as the Gaussian measure of a measurable preimage (`averagedGaussianIndicator_eq_real_measure`), it suffices to bound that measure. The product standard Gaussian law is a probability measure, so the measure of any measurable set is nonnegative and at most one.

**Key facts.** `BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_eq_real_measure`.
