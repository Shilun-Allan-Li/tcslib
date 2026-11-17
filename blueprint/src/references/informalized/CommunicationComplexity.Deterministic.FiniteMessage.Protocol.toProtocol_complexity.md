<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity preservation under conversion

**Claim.** Converting a deterministic finite-message protocol to a binary protocol preserves its communication complexity.

**Proof.** By the existence theorem for the conversion (`toProtocol_exists`), there is a binary protocol whose complexity equals that of the original finite-message protocol. The conversion `toProtocol` is defined to be the protocol chosen by this existence result, so its complexity is the original protocol's complexity.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_exists`.
