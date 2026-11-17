<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_partitePerfectMatching_le_factorial_bound_strong -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strong Partite Matching Bound

**Claim.** The number of perfect matchings on $2r$ parts of size $k$ is at most $((2r-1)/r)^{rk}(rk)!$.

**Proof.** Represent each graph-theoretic perfect matching as a pairing trace on the full set of partite vertices. The construction sending a matching to its trace is injective (`FABL.graphMatchingFullTrace_injective`), so the number of matchings is at most the number of traces. The graph-matching count agrees with the code-based count in the claim (`FABL.card_graphPartitePerfectMatching_eq_partitePerfectMatching`). The full vertex set has $2rk$ elements, hence the trace bound (`FABL.card_partitePairingTrace_le`) applies with $s=rk$ and gives $((2r-1)/r)^{rk}(rk)!$.

**Key facts.** `FABL.graphMatchingFullTrace_injective`, `FABL.card_graphPartitePerfectMatching_eq_partitePerfectMatching`, `FABL.card_partitePairingTrace_le`.
