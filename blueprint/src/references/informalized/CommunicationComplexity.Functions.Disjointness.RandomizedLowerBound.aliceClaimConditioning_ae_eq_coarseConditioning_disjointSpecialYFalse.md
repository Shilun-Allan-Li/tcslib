<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceClaimConditioning_ae_eq_coarseConditioning_disjointSpecialYFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Almost-Sure Conditioning Agreement

**Claim.** Under the hard distribution conditioned on disjoint inputs and on Bob’s bit at the special coordinate being false, Alice’s conditioning triple $(T,X_{<T},Y_{\ge T})$ agrees almost everywhere with the coarse triple $(T,X_{<T},Y_{>T})$.

**Proof.** By the defining property of the conditioned measure, Bob’s bit at the special coordinate is false almost everywhere (`disjointSpecialYFalseMeasure_ae_specialY_false`). For each sample in this full-measure set, the pointwise identity `aliceClaimConditioning_eq_coarseConditioning_of_specialY_false` applies, giving equality of the two triples. Thus the triples agree almost everywhere under the conditioned measure.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_ae_specialY_false`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceClaimConditioning_eq_coarseConditioning_of_specialY_false`.
