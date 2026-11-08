<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.map_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Mapping Preserves Complexity

**Claim.** Applying any function to the output of a private-coin protocol preserves its communication complexity.

**Proof.** The deterministic protocol theorem states that mapping the output by $g$ preserves complexity (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map_complexity`). A private-coin protocol is a deterministic protocol whose two input types are the corresponding coin-input pairs, and its output mapping is the same deterministic mapping. Applying that theorem to these paired input types gives the claim.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map_complexity`.
