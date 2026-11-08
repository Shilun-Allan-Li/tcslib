<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.perfectMatchingPartner_involutive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involutive matching partner map

**Claim.** For a perfect matching $M$ on $2m$ vertices, applying the map that sends each vertex to its partner twice returns the original vertex.

**Proof.** Fix a vertex $v$. Its partner is adjacent to $v$; by symmetry of adjacency, $v$ is adjacent to that partner. The uniqueness of the partner of any vertex now shows that the partner of the partner of $v$ is $v$. Thus the partner map is an involution.

**Key facts.** `FABL.perfectMatchingPartner_adj`, `FABL.perfectMatchingPartner_unique`.
