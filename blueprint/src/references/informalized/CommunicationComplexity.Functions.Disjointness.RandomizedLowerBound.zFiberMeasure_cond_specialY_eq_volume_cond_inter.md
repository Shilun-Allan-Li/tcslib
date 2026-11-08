<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiberMeasure_cond_specialY_eq_volume_cond_inter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditioning a fiber on a bit event

**Claim.** Conditioning the hard-distribution measure on the fiber $Z=z$ and then on Bob's special bit equaling $b$ is the same as conditioning the hard-distribution measure on the intersection of the fiber and that bit event.

**Proof.** The measure on the fiber is defined by conditioning the hard-distribution measure on the fiber. The conditional-measure intersection identity says that conditioning a measure already conditioned on one measurable event by a second measurable event is equivalent to conditioning the original measure on their intersection. Apply it to the fiber and the event that Bob's special bit equals $b$; in this finite discrete space both events are measurable. This gives the stated equality.
