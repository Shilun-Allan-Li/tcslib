<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.fixedAliceConditioning_ae_eq_coordinateAliceConditioning -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Almost-sure equality of conditioning data

**Claim.** Under the measure conditioned on disjointness, Alice's direct conditioning data agrees almost everywhere with the conditioning data extracted from the generated coordinate vector.

**Proof.** The conditioned measure assigns probability one to samples whose generated input sets are disjoint (`disjointCondMeasure_ae_disjointEvent`). Fix any sample in this full-measure event and compare the two conditioning pairs at each coordinate. The coordinate-vector bit identities on disjoint samples identify its Alice and Bob bits with the sample's own bits (`disjointCoordinateVector_xBit_of_mem_disjointEvent`, `disjointCoordinateVector_yBit_of_mem_disjointEvent`). Applying these identities below $i$ for the Alice prefix and from $i$ onward for the Bob suffix gives equality of the pairs at every coordinate, hence equality of the conditioning functions on this full-measure set.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_ae_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCoordinateVector_xBit_of_mem_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCoordinateVector_yBit_of_mem_disjointEvent`.
