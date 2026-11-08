<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_crossInfo_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing conditional mutual information

**Claim.** For every coordinate $i$, Alice's bit at $i$ and Bob's bits strictly before $i$ have zero conditional mutual information given Alice's stated conditioning pair.

**Proof.** First express the conditioning pair as a recoding of Alice's conditioning bit vector (`coordinateAliceConditioning_eq_recode_condBits`). This recoding is injective (`coordinateAliceConditioningOfCondBits_injective`), so replacing the conditioning vector by that recoding leaves the conditional mutual information unchanged. The result then follows from the vanishing conditional mutual information given Alice's conditioning bit vector (`uniformDisjointCoordinateVector_crossInfo_condBits_eq_zero`).

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateAliceConditioning_eq_recode_condBits`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateAliceConditioningOfCondBits_injective`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_crossInfo_condBits_eq_zero`.
