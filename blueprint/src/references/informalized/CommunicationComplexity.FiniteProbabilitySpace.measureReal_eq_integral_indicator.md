<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.measureReal_eq_integral_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measure as an indicator integral

**Claim.** The real measure of any subset of a finite probability space equals the integral of its indicator function.

**Proof.** The indicator of $S$ takes value one at points in $S$ and zero elsewhere, so it agrees pointwise with the function displayed in the statement. The measure of $S$ is the integral of the constant-one function over $S$, equivalently the integral of the indicator of $S$ over the whole space. Replacing that indicator by its pointwise description yields the result.

**Key facts.** `CommunicationComplexity.FiniteProbabilitySpace.measureReal_eq_integral_indicator_one`.
