<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialCoordinateEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform special coordinate after conditioning

**Claim.** Under the disjoint-conditioned distribution, each coordinate is the special coordinate with probability $1/n$.

**Proof.** Conditioning gives the probability as the original mass of the intersection of the special-coordinate event and the disjointness event, divided by the mass of the disjointness event. The intersection has mass $3/(4n)$ (`measureReal_specialCoordinateEvent_inter_disjointEvent`), and the conditioning event has mass $3/4$ (`measureReal_disjointEvent`). Their ratio is $1/n$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialCoordinateEvent_inter_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_disjointEvent`.
