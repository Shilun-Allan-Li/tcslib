<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.aux_disjoint_bob_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjointness of Opposite Bob Branches

**Claim.** Leaf rectangles from distinct Bob branches, restricted to inputs satisfying different values of Bob’s bit function, are disjoint.

**Proof.** If a point $(x,y)$ belonged to both rectangles, the Bob-branch restriction would imply both $f(y)=b$ and $f(y)=b'$, using the fact that every point in a Bob-restricted leaf rectangle satisfies its restriction (`CommunicationComplexity.Deterministic.Protocol.aux_bob_bit`). This contradicts $b\ne b'$, so the rectangles are disjoint.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.aux_bob_bit`.
