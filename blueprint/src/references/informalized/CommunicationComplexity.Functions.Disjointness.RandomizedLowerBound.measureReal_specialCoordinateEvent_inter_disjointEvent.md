<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialCoordinateEvent_inter_disjointEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Special Coordinate and Disjointness

**Claim.** For any fixed coordinate $i$, the event that $T=i$ and the generated sets are disjoint has probability $3/(4n)$.

**Proof.** The disjointness event is the complement of the special-intersection event (`disjointEvent_eq_compl_specialIntersect`). Consequently, among samples with $T=i$, the disjoint samples are exactly those outside the intersection of that coordinate event with the special-intersection event. The measure is therefore the measure of $\{T=i\}$ minus the measure of its intersection with the special-intersection event. These two masses are $1/n$ (`measureReal_specialCoordinateEvent`) and $1/(4n)$ (`measureReal_specialCoordinateEvent_inter_specialIntersect`), respectively. Subtracting gives $1/n-1/(4n)=3/(4n)$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointEvent_eq_compl_specialIntersect`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialCoordinateEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialCoordinateEvent_inter_specialIntersect`.
