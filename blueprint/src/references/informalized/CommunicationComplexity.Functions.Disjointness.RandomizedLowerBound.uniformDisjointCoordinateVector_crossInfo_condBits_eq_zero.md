<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_crossInfo_condBits_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing conditional mutual information

**Claim.** Given Alice's conditioning vector, Alice's bit at coordinate $i$ and Bob's bits strictly before $i$ have zero conditional mutual information.

**Proof.** Write the conditional mutual information as a sum over possible values of the conditioning vector. For each such value, the conditional law makes Alice's bit at $i$ independent of Bob's earlier-bit vector, by the stated conditional-independence result (`uniformDisjointCoordinateVector_indep_coordinateXBit_coordinateYBefore_condBits`). Independence implies that their mutual information under this conditional law is zero. Thus every summand vanishes, and so does the sum.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_indep_coordinateXBit_coordinateYBefore_condBits`.
