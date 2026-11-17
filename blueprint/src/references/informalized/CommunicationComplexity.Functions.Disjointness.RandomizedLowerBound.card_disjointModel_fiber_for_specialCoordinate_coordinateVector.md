<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.card_disjointModel_fiber_for_specialCoordinate_coordinateVector -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting fixed model coordinates and labels

**Claim.** For a fixed special coordinate and a fixed coordinate-label vector, there are exactly three model values with those data, one for each possible ignored label.

**Proof.** The equivalence `disjointModelFiberForSpecialCoordinateCoordinateVectorEquiv` identifies the model values satisfying the two fixed-coordinate constraints with the type of disjoint-coordinate labels: the only remaining free component is the ignored label. Therefore this fiber has the same cardinality as `DisjointCoordinate`, which is $3$ (`DisjointCoordinate.card`).

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.DisjointCoordinate.card`.
