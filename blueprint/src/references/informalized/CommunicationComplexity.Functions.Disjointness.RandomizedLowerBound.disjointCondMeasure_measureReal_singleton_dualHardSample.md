<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_singleton_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual equality of conditioned point masses

**Claim.** For every sample, its dual has the same singleton mass as the sample under the distribution conditioned on disjointness.

**Proof.** Conditioning expresses each singleton mass as the original mass of its intersection with the disjointness event, divided by the mass of that event. Split according to whether $\omega$ belongs to the disjointness event. In the affirmative case, duality preserves membership in that event (`disjointEvent_dualHardSample`), so both intersections are their respective singletons; those singletons have equal original mass (`volume_measureReal_singleton_dualHardSample`). In the negative case, the same equivalence shows that the dual also lies outside the event, so both intersections are empty and both conditioned masses are zero. This proves equality in either case.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointEvent_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measureReal_singleton_dualHardSample`.
