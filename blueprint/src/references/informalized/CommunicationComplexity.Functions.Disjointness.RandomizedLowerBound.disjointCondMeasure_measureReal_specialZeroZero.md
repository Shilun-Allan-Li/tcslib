<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialZeroZero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional probability of two zero bits

**Claim.** For every positive integer $n$, under the uniform hard-sample distribution conditioned on disjointness, the probability that both special bits are false is $1/3$.

**Proof.** Every sample with both special bits false has disjoint input sets (`specialZeroZero_subset_disjointEvent`), so intersecting the event of two zero bits with the disjointness event leaves it unchanged. Its measure is $1/4$ (`measureReal_specialZeroZero`), and the disjointness event has measure $3/4$ (`measureReal_disjointEvent`). Dividing gives $(1/4)/(3/4)=1/3$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialZeroZero_subset_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialZeroZero`.
