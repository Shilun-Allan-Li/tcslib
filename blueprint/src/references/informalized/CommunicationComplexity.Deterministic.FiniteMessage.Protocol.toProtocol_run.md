<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output preservation under conversion

**Claim.** For every input pair, the binary protocol obtained by converting a deterministic finite-message protocol returns the same output as the original protocol.

**Proof.** The existence theorem `toProtocol_exists` supplies a protocol chosen by `toProtocol` whose run function equals the original protocol's run function. Evaluating this function equality at any input pair gives the claimed equality of outputs.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_exists`.
