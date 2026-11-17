<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.eq_of_deletePath_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# When Deletion Is Undefined

**Claim.** If deleting the path from $p$ to $s$ returns nothing, then $s=p$.

**Proof.** Proceed by cases on the path. For the reflexive path, the two protocols are equal. In each non-reflexive case, the path enters one child of a protocol node. Deleting the subpath either returns nothing, in which case the defining equation for deletion at the current node shows that the full deletion returns a protocol in the opposite child, or returns a protocol, in which case the full deletion reconstructs a protocol node. Both possibilities contradict the assumption that deletion returns nothing. Hence no non-reflexive path is possible, and the reflexive case gives $s=p$.
