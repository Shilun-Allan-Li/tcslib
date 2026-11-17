<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiberMeasure_inter_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support of the fiber-conditioned measure

**Claim.** For every set $S$ of hard-distribution samples, the real measure of the intersection of the fiber $Z=z$ with $S$, under the measure conditioned on that fiber, equals the real measure of $S$ under that same conditioned measure.

**Proof.** The fiber-conditioned measure is the original measure conditioned on the fiber. A conditional measure gives zero mass outside its conditioning event, so intersecting any set $S$ with that event does not change its measure (`cond_inter_self`). Passing to real-valued measures preserves the equality, yielding the claim.
