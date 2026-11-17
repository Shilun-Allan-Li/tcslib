<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncHash.lean :: CommunicationComplexity.Functions.Hash.collisionPiece_pairwiseDisjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint collision pieces

**Claim.** Collision pieces associated with distinct common hash values are pairwise disjoint.

**Proof.** Suppose a hash function belonged to the pieces for two distinct values $a$ and $b$. Membership in the first piece forces its value at $x$ to be $a$, while membership in the second forces that same value to be $b$. Hence $a=b$, contradicting their assumed distinctness. Therefore the two pieces have empty intersection.
