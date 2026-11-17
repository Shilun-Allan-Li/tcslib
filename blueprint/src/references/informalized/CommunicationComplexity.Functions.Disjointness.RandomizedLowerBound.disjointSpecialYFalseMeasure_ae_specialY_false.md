<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_ae_specialY_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Almost-sure special bit under conditioning

**Claim.** Under the measure conditioned on disjointness and then on Bob's special bit being false, Bob's special bit is false almost surely.

**Proof.** The second conditioning restricts the disjoint-conditioned measure to the event where the special bit is false. Under a measure restricted to an event, that event holds almost surely (`ae_cond_mem`). Therefore the special bit equals false almost everywhere under the doubly conditioned measure.
