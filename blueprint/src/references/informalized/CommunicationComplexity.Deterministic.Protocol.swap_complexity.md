<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean :: CommunicationComplexity.Deterministic.Protocol.swap_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Role Swap Preserves Complexity

**Claim.** The role-swapped protocol has the same communication complexity as the original protocol.

**Proof.** Induct on the protocol. At an output node, both complexities are zero. At an Alice node, role swap turns the node into a Bob node and swaps each child protocol; the induction hypotheses identify the complexities of the swapped children with those of the original children. Both node complexities are therefore one plus the maximum of the same two child complexities. At a Bob node, the same reasoning applies with Alice and Bob interchanged.
