<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZVariable.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualProtocolTranscriptMap_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the transcript duality map

**Claim.** The map sending a protocol transcript to the corresponding transcript of the dual protocol is injective.

**Proof.** The map is the composition of two maps: first, transcript swapping, which preserves the sequence of Boolean messages while exchanging the protocol roles; second, transcript transport along the input reindexings defining the dual protocol. Transcript swapping is injective (`transcriptSwap_injective`), and transport along the input maps is injective (`transcriptComap_injective`). A composition of injective maps is injective, proving the claim.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.transcriptSwap_injective`, `CommunicationComplexity.Deterministic.Protocol.transcriptComap_injective`.
