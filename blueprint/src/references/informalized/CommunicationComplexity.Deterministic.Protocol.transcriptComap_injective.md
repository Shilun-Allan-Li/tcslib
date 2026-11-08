<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Transcript.lean :: CommunicationComplexity.Deterministic.Protocol.transcriptComap_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of transcript pull-back

**Claim.** For any input maps, the map sending a protocol transcript to the corresponding transcript of the pulled-back protocol is injective.

**Proof.** Proceed by induction on the protocol. At a terminal node there is only one transcript, so injectivity is immediate. At either kind of communication node, a transcript consists of its first Boolean message together with a transcript of the selected child. The pull-back preserves that first message and applies the corresponding transcript map to the child transcript. By the induction hypothesis each child map is injective; the fact that a map of dependent pairs is injective when it preserves the first coordinate and is injective on each fiber (the Boolean sigma-map injectivity lemma, `sigma_map_bool_injective`) now gives injectivity at the node.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.sigma_map_bool_injective`.
