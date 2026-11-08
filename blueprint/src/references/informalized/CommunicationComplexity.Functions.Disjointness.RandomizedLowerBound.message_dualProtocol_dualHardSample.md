<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.message_dualProtocol_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality Commutes with Protocol Execution

**Claim.** Running the dual protocol on the dual hard sample yields the transcript obtained by applying the transcript recoding induced by duality to the original transcript.

**Proof.** First express the dual input as the reversed Bob set followed by the reversed Alice set (`input_dualHardSample`). The transcript of the protocol with its players swapped on this exchanged pair is the swapped transcript of the original protocol (`transcriptSwap_transcript`). Apply the transcript compatibility of input reparameterization (`transcriptComap_transcript`) to the two coordinate-reversal maps. Since reversing a set twice returns the original set (`reverseSet_reverseSet`), the resulting transcript is precisely the stated recoding of the original transcript.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.input_dualHardSample`, `CommunicationComplexity.Deterministic.Protocol.transcriptComap_transcript`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.reverseSet_reverseSet`, `CommunicationComplexity.Deterministic.Protocol.transcriptSwap_transcript`.
