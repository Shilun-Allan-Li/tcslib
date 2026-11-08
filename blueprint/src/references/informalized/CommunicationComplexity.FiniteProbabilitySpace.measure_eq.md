<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.measure_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measure as a sum of point masses

**Claim.** For every subset $S$ of a finite probability space, its measure is the sum, over points of $S$, of their probability masses.

**Proof.** View the measure as the measure induced by its associated probability mass function; these measures agree. The measure induced by a probability mass function assigns to a measurable set the sum of the masses of its elements. Since every subset is measurable here, this applies to $S$. The sum over elements of $S$ is precisely the sum over the subtype whose elements are points of $S$, giving the formula.
