<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ofProtocol_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of an Embedded Binary Protocol

**Claim.** Embedding a binary private-coin protocol into the finite-message protocol representation preserves its communication complexity.

**Proof.** The deterministic theorem for embedding a binary protocol into the finite-message representation asserts that the two complexities agree (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_complexity`). Apply it to the underlying deterministic protocol on the paired coin-input spaces $(\Omega_X\times X)$ and $(\Omega_Y\times Y)$. The private-coin embedding is this same embedding with those input spaces, so the equality is the desired one.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_complexity`.
