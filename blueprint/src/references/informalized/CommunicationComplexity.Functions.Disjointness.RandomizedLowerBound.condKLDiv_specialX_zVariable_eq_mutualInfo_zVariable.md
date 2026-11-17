<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.condKLDiv_specialX_zVariable_eq_mutualInfo_zVariable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional KL and Mutual Information

**Claim.** Under the hard-sample distribution conditioned on disjoint inputs and Bob’s special bit being false, the conditional KL divergence of Alice’s special bit given the summary equals its mutual information with that summary.

**Proof.** First, the conditioned measure is a probability measure (disjointSpecialYFalseMeasure_isProbabilityMeasure). The law of Alice’s special bit under this measure is uniform (disjointSpecialYFalseMeasure_specialX_law_eq_uniformBool), so its KL divergence from the uniform bit law is zero. The uniform law gives positive mass to each bit (uniformBool_toPMF_ne_zero), ensuring the support condition needed for the conditional-divergence decomposition. That decomposition expresses the conditional KL divergence as the unconditional KL divergence plus the mutual information minus the entropy of the reference law; here, equivalently, it identifies the conditional divergence with mutual information once the unconditional divergence vanishes and the reference law is uniform. Rewriting mutual information by the entropy-minus-conditional-entropy formula yields the stated equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_isProbabilityMeasure`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_specialX_law_eq_uniformBool`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_toPMF_ne_zero`.
