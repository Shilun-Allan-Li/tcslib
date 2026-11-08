<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.fixedYBefore_ae_eq_coordinateYBefore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Almost-sure equality of Bob's prefix

**Claim.** Under the disjoint-conditioned hard measure, Bob's padded prefix agrees almost everywhere with the prefix extracted from the generated disjoint coordinate vector.

**Proof.** The conditioned measure gives probability one to samples in the disjoint event (`disjointCondMeasure_ae_disjointEvent`). Fix such a sample. At a coordinate below $i$, the generated coordinate's $y$-bit equals Bob's bit (`disjointCoordinateVector_yBit_of_mem_disjointEvent`), so the prefix values agree there. At a coordinate not below $i$, both prefix functions are false by definition. Thus the functions agree at every coordinate for each sample in this full-measure event.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_ae_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCoordinateVector_yBit_of_mem_disjointEvent`.
