<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.epsilon_pow_four_div_nine_le_boundedDecodingEdgeValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Edge Decoding Bound

**Claim.** Under the two stated influence conditions, the bounded decoding value on the directed edge is at least $\varepsilon^4/9$.

**Proof.** Let $C_s$ and $C_t$ be the source and target candidate sets, and let $j$ be the inverse-permuted image of the given coordinate. The two influence hypotheses put the coordinate in $C_s$ and $j$ in $C_t$. In particular both sets are nonempty. The candidate-count estimate (`card_boundedDecodingCandidates_le`) bounds each set's size by $3/\varepsilon^2$; the reciprocal-count inequality (`epsilon_sq_div_three_le_inv_card`) then gives $\varepsilon^2/3\le 1/|C_s|$ and $\varepsilon^2/3\le 1/|C_t|$. The constraint permutation sends $j$ to the source coordinate, so this pair satisfies the edge relation. The finite-candidate pair estimate (`finiteCandidatePairExpectation_ge`) says that this matching pair contributes at least $1/(|C_s||C_t|)$ to the edge value. Multiplying the reciprocal bounds yields $\varepsilon^4/9\le 1/(|C_s||C_t|)$, proving the result.

**Key facts.** `FABL.RegularUniqueGame.card_boundedDecodingCandidates_le`, `FABL.RegularUniqueGame.epsilon_sq_div_three_le_inv_card`, `FABL.RegularUniqueGame.finiteCandidatePairExpectation_ge`.
