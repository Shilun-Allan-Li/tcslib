<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toProtocol_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity preserved under protocol conversion

**Claim.** The binary public-coin protocol obtained by converting a public-coin finite-message protocol has the same communication complexity as the original.

**Proof.** The converted protocol is the deterministic binary protocol associated with the finite-message protocol. The finite-message conversion theorem states that this conversion preserves complexity (`Deterministic.FiniteMessage.Protocol.toProtocol_complexity`), giving the claimed equality.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_complexity`.
