<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.prunePath_numLeaves_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leaf Count After Path Pruning

**Claim.** If a specified path leads from $p$ to a proper subprotocol $s$ with fewer leaves, pruning that path from $p$ produces a protocol with $\mathrm{numLeaves}(p)-\mathrm{numLeaves}(s)$ leaves.

**Proof.** The pruned protocol is chosen so that deleting the specified path returns it. The leaf-count formula for any protocol returned by path deletion therefore applies: its number of leaves is the original count minus the count of the subtree at the end of the path. Substituting the pruned protocol for that returned protocol gives the stated equality.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.deletePath_numLeaves_of_some`, `CommunicationComplexity.Deterministic.Protocol.prunePath_spec`.
