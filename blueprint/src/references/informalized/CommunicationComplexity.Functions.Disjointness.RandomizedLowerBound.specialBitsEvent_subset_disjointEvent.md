<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialBitsEvent_subset_disjointEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjointness from the Special Bits

**Claim.** If the prescribed special bits are not both true, then every hard sample with those special bits generates disjoint input sets.

**Proof.** Take a sample in the special-bits event. The characterization of disjointness for the generated input sets says that they are disjoint exactly when the sample's two special bits are not both true (`disjoint_X_Y_iff`). If the generated sets were not disjoint, that characterization would force both special bits to be true. Since the sample's bits equal the prescribed pair, this contradicts the hypothesis that the prescribed bits are not both true. Therefore the generated sets are disjoint.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjoint_X_Y_iff`.
