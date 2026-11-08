<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.message_ae_eq_coordinateMessage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Almost-Sure Transcript Reconstruction

**Claim.** Under the hard distribution conditioned on disjointness, running the protocol on the sample’s generated input sets gives almost surely the same transcript as running it on the input sets reconstructed from its disjoint coordinate vector.

**Proof.** The conditioned measure is concentrated on samples whose generated input sets are disjoint (`disjointCondMeasure_ae_disjointEvent`). Fix any such sample. At each coordinate, the reconstructed disjoint coordinate has the same Alice bit as the original sample (`disjointCoordinateVector_xBit_of_mem_disjointEvent`) and the same Bob bit (`disjointCoordinateVector_yBit_of_mem_disjointEvent`). Thus the two reconstructed input sets agree coordinate by coordinate with the original input sets. The protocol therefore receives the same input pair and produces the same transcript, proving the asserted almost-sure equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_ae_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCoordinateVector_xBit_of_mem_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCoordinateVector_yBit_of_mem_disjointEvent`.
