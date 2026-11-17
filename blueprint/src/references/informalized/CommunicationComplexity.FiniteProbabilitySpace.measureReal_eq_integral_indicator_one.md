<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.measureReal_eq_integral_indicator_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator integral formula

**Claim.** For any subset $S$ of a finite probability space, its real-valued probability equals the integral of its indicator function.

**Proof.** Because the space has the discrete measurable structure, every subset $S$ is measurable. The integral of the indicator of a measurable set against a measure is the measure of that set. Applying this identity gives the asserted equality.
