<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialBitsEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform special-bit values after conditioning

**Claim.** For any prescribed pair of special-bit values that are not both true, the conditioned probability of that pair is $1/3$.

**Proof.** The event prescribing the two special bits is contained in the disjointness event whenever the bits are not both true (`specialBitsEvent_subset_disjointEvent`). Therefore its intersection with the conditioning event is just the special-bit event itself. The conditional probability is the ratio of the original probabilities: the special-bit event has mass $1/4$ (`measureReal_specialBitsEvent`), while the full disjointness event has mass $3/4$ (`measureReal_disjointEvent`). Their ratio is $(1/4)/(3/4)=1/3$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialBitsEvent_subset_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialBitsEvent`.
