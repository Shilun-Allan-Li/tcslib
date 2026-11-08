<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Transcript.lean :: CommunicationComplexity.Deterministic.Protocol.transcriptSwap_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of transcript swap

**Claim.** The map sending a transcript to the corresponding transcript of the role-swapped protocol is injective.

**Proof.** Proceed by induction on the protocol. At a terminal node the transcript is the unique empty transcript, so the map is injective. At a communication node, a transcript consists of its Boolean message and the transcript of the selected child. Swapping roles preserves the message and applies transcript swap recursively to the child. The induction hypothesis gives injectivity for each child map, and the Boolean sigma-map injectivity lemma (`sigma_map_bool_injective`) then gives injectivity for the full transcript map.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.sigma_map_bool_injective`.
