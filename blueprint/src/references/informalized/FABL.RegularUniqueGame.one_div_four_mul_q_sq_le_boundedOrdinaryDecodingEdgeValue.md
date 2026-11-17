<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.one_div_four_mul_q_sq_le_boundedOrdinaryDecodingEdgeValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for the Decoding Edge Value

**Claim.** If a coordinate is influential for the averaged neighbor function at a vertex and its inverse image under the constraint permutation is influential at the neighbor, then the ordinary candidate-decoding edge value is at least $1/(4q^2)$.

**Proof.** Let the source and target candidate sets be the ordinary decoding candidate sets at the vertex and its neighbor, respectively. The two influence hypotheses put the specified coordinate in the source set and its inverse image in the target set, so both sets are nonempty. Each set has size at most $2q$ by the candidate-count bound (`card_boundedOrdinaryDecodingCandidates_le`). The reciprocal candidate-count bound (`one_div_two_mul_q_le_inv_card`) thus gives a reciprocal size of at least $1/(2q)$ for each set. The specified source and target labels satisfy the constraint, since the permutation sends the inverse image of the source coordinate back to that coordinate. Hence the nested uniform candidate average assigns this agreeing pair weight at least the reciprocal of the product of the two set sizes (`finiteCandidatePairExpectation_ge`). Multiplying the two reciprocal bounds gives at least $1/(4q^2)$, and the nested average is the ordinary decoding edge value by definition.

**Key facts.** `FABL.RegularUniqueGame.card_boundedOrdinaryDecodingCandidates_le`, `FABL.RegularUniqueGame.one_div_two_mul_q_le_inv_card`, `FABL.RegularUniqueGame.finiteCandidatePairExpectation_ge`.
