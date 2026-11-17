<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean :: CommunicationComplexity.Deterministic.Protocol.swap_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Role Swap Is an Involution

**Claim.** Applying role swap twice to a protocol returns the original protocol.

**Proof.** Induct on the protocol. An output node is unchanged by either swap. For an Alice node, the first swap makes it a Bob node with each child swapped; the second makes it an Alice node again. Applying the induction hypothesis to each child shows that every child is restored, so the original node is recovered. The Bob case is symmetric.
