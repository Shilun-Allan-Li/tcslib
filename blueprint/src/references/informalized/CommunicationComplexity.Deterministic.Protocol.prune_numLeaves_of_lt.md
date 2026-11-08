<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.prune_numLeaves_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leaf Count After Subprotocol Pruning

**Claim.** If $s$ is a subprotocol of $p$ and has strictly fewer leaves, pruning $s$ from $p$ yields a protocol with $\mathrm{numLeaves}(p)-\mathrm{numLeaves}(s)$ leaves.

**Proof.** Choose a path witnessing that $s$ is a subprotocol of $p$, and prune along this path. The path-pruning leaf-count result gives the pruned protocol’s count as the count of $p$ minus that of $s$. Since pruning a subprotocol is defined to be this path-pruned protocol, the same equality holds for the stated pruning.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.prunePath_numLeaves_of_lt`.
