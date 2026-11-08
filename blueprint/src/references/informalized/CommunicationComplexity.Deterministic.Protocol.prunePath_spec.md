<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.prunePath_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of Path Pruning

**Claim.** If a path leads from $p$ to $s$ and $s$ has strictly fewer leaves than $p$, deleting that path returns the pruned protocol as a genuine protocol.

**Proof.** The strict leaf-count hypothesis ensures that path deletion returns some protocol. By definition, the pruned protocol is chosen from a witness to this existence statement. The specification of that chosen witness says exactly that deleting the path returns the pruned protocol.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.deletePath_exists_of_lt`.
