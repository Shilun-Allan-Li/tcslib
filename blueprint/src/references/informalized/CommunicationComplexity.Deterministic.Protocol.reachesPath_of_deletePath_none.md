<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.reachesPath_of_deletePath_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trivial path is always reached

**Claim.** If deleting a subprotocol path returns no protocol, every input pair reaches the endpoint of that path.

**Proof.** Induct on the path. For a trivial path, both reachability sets are the entire input spaces, so every pair reaches the endpoint. At an Alice branch, consider whether deleting the remaining path returns no protocol or a protocol. In the latter case, deleting the whole path returns a protocol, contradicting the hypothesis; hence the remaining path also deletes to none, and the induction hypothesis gives reachability for both parties. The additional Alice consistency condition required by the path is automatic: if her branch condition failed, the deletion rule would retain the opposite branch and return a protocol. The Bob cases are the same, with the consistency condition imposed on Bob's input instead.
