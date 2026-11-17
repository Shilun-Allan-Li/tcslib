<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_disjointEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass of the Disjointness Event

**Claim.** Under the uniform measure on hard samples, the disjointness event has measure $3/4$.

**Proof.** The disjointness event is the complement of the event that the two generated sets intersect (`disjointEvent_eq_compl_specialIntersect`). Thus its measure is the total mass $1$ minus the mass of that special intersection event. The latter has measure $1/4$ (`measureReal_specialIntersect`), so the disjointness event has measure $1-1/4=3/4$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointEvent_eq_compl_specialIntersect`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialIntersect`.
