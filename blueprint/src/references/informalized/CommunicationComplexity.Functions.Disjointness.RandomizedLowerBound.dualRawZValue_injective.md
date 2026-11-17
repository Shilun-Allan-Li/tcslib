<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualRawZValue_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of raw Z-value dualization

**Claim.** The dualization map on raw $Z$-values is injective.

**Proof.** Suppose two raw $Z$-values have the same dual. Compare their fields. Equality of the dual transcripts implies equality of the original transcripts because the transcript duality map is injective (`dualProtocolTranscriptMap_injective`). Equality of the reversed special coordinates implies equality of the original coordinates, since reversing a coordinate is an involution. Equality of the dual before-vectors and after-vectors gives equality of the corresponding original vectors: each is obtained by reversing the other vector, and vector reversal is injective (`reverseBoolVector_injective`). Thus all four fields agree, and the raw $Z$-values are equal by the extensionality principle for their fields (`RawZType.ext`).

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.RawZType.ext`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualProtocolTranscriptMap_injective`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.reverseBoolVector_injective`.
