<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.measurableSet_indicatorDisagreement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of Membership Disagreement

**Claim.** For measurable maps into a measurable space and a measurable set, the points where exactly one image belongs to the set form a measurable set.

**Proof.** The preimages of $A$ under $f$ and $g$ are measurable, because $A$ and both maps are measurable. The set where exactly one of $f(z)$ and $g(z)$ belongs to $A$ is the symmetric difference of these two preimages. A symmetric difference of measurable sets is measurable, proving the claim.
