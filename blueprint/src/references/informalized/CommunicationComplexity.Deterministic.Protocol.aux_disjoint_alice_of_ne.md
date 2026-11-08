<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.aux_disjoint_alice_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjointness of Opposite Alice Branches

**Claim.** Leaf rectangles from distinct Alice branches, restricted to inputs satisfying different values of Alice’s bit function, are disjoint.

**Proof.** Suppose a point $(x,y)$ belonged to both rectangles. The branch restriction forces $f(x)=b$ for the first rectangle and $f(x)=b'$ for the second, by the fact that every point in an Alice-restricted leaf rectangle satisfies its restriction (`CommunicationComplexity.Deterministic.Protocol.aux_alice_bit`). These equalities imply $b=b'$, contradicting their assumed distinctness. Thus the rectangles have no common point.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.aux_alice_bit`.
