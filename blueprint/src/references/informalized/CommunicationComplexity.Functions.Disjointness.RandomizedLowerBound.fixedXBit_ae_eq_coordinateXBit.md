<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.fixedXBit_ae_eq_coordinateXBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Almost-sure equality of Alice's bit

**Claim.** Under the disjoint-conditioned hard measure, Alice's bit at any fixed coordinate agrees almost everywhere with the $x$-bit of the generated disjoint coordinate at that coordinate.

**Proof.** The conditioned measure gives probability one to samples in the disjoint event (`disjointCondMeasure_ae_disjointEvent`). On each such sample, the generated coordinate's $x$-bit equals Alice's bit at the same coordinate (`disjointCoordinateVector_xBit_of_mem_disjointEvent`). Reversing this equality gives the claimed almost-sure agreement.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_ae_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCoordinateVector_xBit_of_mem_disjointEvent`.
