<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.measurableSet_densityPositiveSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of the density threshold set

**Claim.** The set on which the real-valued Radon–Nikodym density is at least one is measurable.

**Proof.** The density is measurable (`CommunicationComplexity.measurable_rnDensity`). The interval $[1,\infty)$ is a Borel set, and the inverse image of a measurable interval under a measurable function is measurable. That inverse image is precisely the set where the density is at least one.

**Key facts.** `CommunicationComplexity.measurable_rnDensity`.
