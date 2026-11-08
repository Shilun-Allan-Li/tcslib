<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_disjointModel_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass of a disjoint-model fiber

**Claim.** Every specified triple consisting of a special coordinate, a disjoint coordinate vector, and an ignored coordinate has conditional probability $1/(n\cdot 3^n\cdot 3)$.

**Proof.** Write the event in question as the preimage under the disjoint model of the condition that its first component is $i$ and its second component is the prescribed coordinate vector. The measure of such a preimage is the sum of the measures of the individual fibers satisfying that condition (finite preimage measure as a sum over fibers, `FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers`). Each individual fiber has mass $1/(n\cdot 3^n\cdot 3)$ (`disjointCondMeasure_measureReal_disjointModel_fiber`). There are exactly three eligible triples, one for each possible ignored coordinate (`card_disjointModel_fiber_for_specialCoordinate_coordinateVector`). Summing their equal masses gives $3/(n\cdot 3^n\cdot 3)=1/(n\cdot 3^n)$ for the event specifying only the first two components; equivalently, each full triple has the claimed mass. Since the full model space has $n\cdot 3^n\cdot 3$ elements, this is its uniform law.

**Key facts.** `CommunicationComplexity.FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_disjointModel_fiber`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.card_disjointModel_fiber_for_specialCoordinate_coordinateVector`.
