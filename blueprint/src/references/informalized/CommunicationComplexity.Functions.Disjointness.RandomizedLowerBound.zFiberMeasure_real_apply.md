<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiberMeasure_real_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized measure on a fiber

**Claim.** The real measure of a set $S$ under the hard-distribution measure conditioned on the fiber $Z=z$ equals the reciprocal of the real measure of that fiber multiplied by the real measure of its intersection with $S$.

**Proof.** By definition, the fiber-conditioned measure is the original hard-distribution measure conditioned on the fiber. The real-valued formula for conditioning on a measurable event expresses the measure of $S$ as the reciprocal of the event's real measure times the original measure of the intersection of the event with $S` (`cond_real_apply`). The fiber is measurable in the discrete space, so this formula applies and gives the asserted identity.
