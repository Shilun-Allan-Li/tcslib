<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialY_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional special-bit probability

**Claim.** For every positive integer $n$, under the uniform hard-sample distribution conditioned on disjointness, the probability that Bob's special bit is false is $2/3$.

**Proof.** The conditional probability is the measure of the intersection of the disjointness event with the event that the special bit is false, divided by the measure of the disjointness event. Whenever the special bit is false, the inputs are disjoint (`mem_disjointEvent_of_specialY_eq_false`), so this intersection is just the special-bit-false event. Its measure is $1/2$ (`measureReal_specialY_false`), while the disjointness event has measure $3/4$ (`measureReal_disjointEvent`). Thus the conditional probability is $(1/2)/(3/4)=2/3$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mem_disjointEvent_of_specialY_eq_false`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialY_false`.
