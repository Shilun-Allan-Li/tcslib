<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.epsilon_pow_four_div_nine_le_decodingEdgeValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Edge Decoding Bound

**Claim.** Under the two stated influence conditions, the decoding value on the directed edge is at least $\varepsilon^4/9$.

**Proof.** Let $C_s$ and $C_t$ be the source and target candidate sets, and let $j$ be the inverse-permuted image of the given coordinate. The hypotheses place the coordinate in $C_s$ and $j$ in $C_t$, so both candidate sets are nonempty. By the candidate-count bound (`card_decodingCandidates_le`), each has size at most $3/\varepsilon^2$. The reciprocal-count inequality (`epsilon_sq_div_three_le_inv_card`) therefore gives $\varepsilon^2/3\le 1/|C_s|$ and $\varepsilon^2/3\le 1/|C_t|$. Since the constraint permutation sends $j$ to the source coordinate, this pair matches. The finite-candidate pair estimate (`finiteCandidatePairExpectation_ge`) bounds the edge value below by $1/(|C_s||C_t|)$. Multiplying the reciprocal bounds gives the claimed $\varepsilon^4/9$.

**Key facts.** `FABL.RegularUniqueGame.card_decodingCandidates_le`, `FABL.RegularUniqueGame.epsilon_sq_div_three_le_inv_card`, `FABL.RegularUniqueGame.finiteCandidatePairExpectation_ge`.
