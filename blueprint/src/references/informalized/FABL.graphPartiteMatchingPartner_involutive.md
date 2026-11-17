<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphPartiteMatchingPartner_involutive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involutive Matching Partner Map

**Claim.** The map sending each vertex to its matching partner is an involution: applying it twice returns the original vertex.

**Proof.** Fix a vertex $v$. Its partner is adjacent to $v$; by symmetry, $v$ is adjacent to that partner. The uniqueness property of matching partners, applied at the partner vertex, then says that $v$ is the partner's matching partner. This proves the involution identity (`graphPartiteMatchingPartner_adj`, `graphPartiteMatchingPartner_unique`).

**Key facts.** `FABL.graphPartiteMatchingPartner_adj`, `FABL.graphPartiteMatchingPartner_unique`.
