<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.perfectMatchingPartnerPerm_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Matching Permutations

**Claim.** For every natural number $m$, distinct perfect matchings of the complete graph on $2m$ vertices yield distinct associated permutations.

**Proof.** Suppose two matchings give the same permutation. At each vertex, their partner permutations consequently agree. To show the matchings have the same edges, consider an edge $\{u,v\}$ in the first matching. The uniqueness of the matched partner (`perfectMatchingPartner_unique`) identifies $v$ as the first matching's partner of $u$. Equality of the partner permutations makes it the second matching's partner as well, so that edge belongs to the second matching (`perfectMatchingPartner_adj`). The same argument with the matchings exchanged gives the reverse inclusion of edges. Their vertex sets are both the full vertex set, so the matchings are equal.

**Key facts.** `FABL.perfectMatchingPartner_unique`, `FABL.perfectMatchingPartner_adj`.
