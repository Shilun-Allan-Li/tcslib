<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingFullTrace_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Full Matching Trace

**Claim.** For $r>0$, the full greedy pairing trace determines a perfect matching in the complete $2r$-partite graph with $k$ vertices per part.

**Proof.** Suppose two perfect matchings have the same full trace. The full vertex set has cardinality $2(rk)$, and each matching is closed on that set because every partner is a vertex. The theorem that equal traces on a closed remaining set determine the same partner for every vertex in that set (graphMatchingTrace_partner_eq_on_remaining) thus shows that the two matchings assign every vertex the same partner.

It remains to show that their edge sets agree. Each matching has all vertices, by the perfect-matching property. If $u$ is adjacent to $v$ in the first matching, uniqueness of the matching partner gives that $v$ is the first matching’s partner of $u$. The partner equality makes it the second matching’s partner as well; the second matching contains the edge from $u$ to that partner. This proves inclusion of the first edge set in the second, and the same argument with the matchings reversed proves the converse. Hence the matchings are equal.

**Key facts.** `FABL.graphMatchingClosedOn_univ`, `FABL.graphMatchingTrace_partner_eq_on_remaining`, `FABL.graphPartiteMatchingPartner_unique`, `FABL.graphPartiteMatchingPartner_adj`.
