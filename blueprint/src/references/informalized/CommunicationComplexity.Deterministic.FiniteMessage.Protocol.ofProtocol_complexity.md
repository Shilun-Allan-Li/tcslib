<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of an embedded binary protocol

**Claim.** Embedding a deterministic binary protocol in the finite-message framework preserves its communication complexity.

**Proof.** Proceed by structural induction on the binary protocol. At an output node both complexities are zero. At an Alice node, the embedded protocol still sends a Boolean message, whose alphabet has cardinality two. Its cost is therefore $\lceil\log_2 2\rceil=1$, and its continuation supremum is the maximum of the complexities of the false and true branches. By induction these branch complexities equal those in the binary protocol, whose node cost is also one plus that maximum. The Bob node has the same calculation. Thus the complexities agree at every node.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.clog_two_two`.
