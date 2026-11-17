<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of the finite-message embedding

**Claim.** Embedding a binary public-coin protocol into the finite-message framework preserves its worst-case communication complexity.

**Proof.** Regard the public-coin protocol as a deterministic protocol whose inputs are the shared-randomness and private-input pairs. The deterministic embedding theorem states that converting each Boolean-message branch to a finite-message branch preserves complexity (\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol\_complexity}). Applying it to this protocol gives the claimed equality.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_complexity`.
