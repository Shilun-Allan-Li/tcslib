<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.prunePath_run_outside_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution Outside a Pruned Path

**Claim.** For inputs that do not reach the specified path, pruning that path leaves the protocol’s output unchanged.

**Proof.** The pruned protocol is the protocol returned by deleting the specified path, by the specification of path pruning. The deletion lemma states that on any input pair not reaching the path, the protocol returned by deletion has the same output as the original protocol. Applying that lemma to the pruned protocol gives the claimed equality.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.deletePath_run_outside_of_some`, `CommunicationComplexity.Deterministic.Protocol.prunePath_spec`.
