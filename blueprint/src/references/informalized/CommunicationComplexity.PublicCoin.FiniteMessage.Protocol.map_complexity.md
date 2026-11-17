<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.map_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output mapping preserves complexity

**Claim.** Applying any function $g\colon\alpha\to\beta$ to the output of a public-coin protocol preserves its communication complexity.

**Proof.** The public-coin protocol is an instance of the deterministic finite-message protocol on paired inputs, and its output map is the same recursive map on protocol trees. The deterministic result that mapping outputs leaves complexity unchanged (\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map\_complexity}) therefore applies directly.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map_complexity`.
