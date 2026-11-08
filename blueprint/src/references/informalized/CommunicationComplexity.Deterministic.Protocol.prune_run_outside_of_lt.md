<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.prune_run_outside_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pruning preserves outside outputs

**Claim.** If a proper subprotocol is deleted from a protocol, every input pair that does not reach that subprotocol has the same output as before.

**Proof.** Choose the path witnessing that $s$ is a subprotocol of $p$. The path-level pruning result says that, for any input pair that does not reach along this path, running the pruned protocol gives the same output as running $p$ (`prunePath_run_outside_of_lt`). By definition, `prune` uses this chosen path, and `reaches` is the corresponding path reachability condition expressed through the chosen path. Substituting these definitions gives the claimed equality.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.prunePath_run_outside_of_lt`.
