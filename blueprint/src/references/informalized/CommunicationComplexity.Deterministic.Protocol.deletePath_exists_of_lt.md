<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.deletePath_exists_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deletion Succeeds Along a Proper Path

**Claim.** If a subprotocol occurs along a path in a protocol and has strictly fewer leaves than the whole protocol, deleting the branch leading to it produces some protocol.

**Proof.** The result follows from the fact that deletion along such a path cannot be empty when the subprotocol has strictly fewer leaves (`deletePath_ne_none_of_lt`). Since deletion is therefore not `none`, it has the form `some q` for a protocol $q$, as required.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.deletePath_ne_none_of_lt`.
