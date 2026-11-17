<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialCoordinate_disjointCoordinateVector_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joint law of coordinate and vector

**Claim.** For each special coordinate and each disjoint coordinate vector, their joint event has conditioned probability $1/(n\cdot 3^n)$.

**Proof.** Express this event as the preimage under the disjoint model of the property that the first component is the specified coordinate and the second component is the specified vector. Its measure is the sum of the masses of all model fibers satisfying that property (`FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers`). There are exactly three such fibers, corresponding to the three choices of ignored coordinate (`card_disjointModel_fiber_for_specialCoordinate_coordinateVector`). Each has mass $1/(n\cdot 3^n\cdot 3)$ (`disjointCondMeasure_measureReal_disjointModel_fiber`), so their sum is $1/(n\cdot 3^n)$.

**Key facts.** `CommunicationComplexity.FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_disjointModel_fiber`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.card_disjointModel_fiber_for_specialCoordinate_coordinateVector`.
