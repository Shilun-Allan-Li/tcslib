<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.perfectMatchingGraphOfCode_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Matching Graph Map

**Claim.** For every natural number $m$, the map sending a code in $\mathrm{PerfectMatchingCode}(m)$ to its associated perfect matching in the complete graph on $2m$ vertices is injective.

**Proof.** Suppose two codes produce the same perfect matching. Equality of these matchings gives equality of their underlying subgraphs, hence equality of their adjacency relations. In particular, their decoded edge graphs agree. The vertex list contains each of the $2m$ vertices exactly once, by `nodup_finVertexList`, and has length $2m$. The injectivity theorem for decoding a code into its pair-list graph (`pairListGraph_decodePerfectMatchingCode_injective`) therefore implies that the two codes are equal.

**Key facts.** `FABL.nodup_finVertexList`, `FABL.pairListGraph_decodePerfectMatchingCode_injective`.
