<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.dictatorIndicator_le_operationalCheckValue_add_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator and operational checks

**Claim.** For a labeling, a vertex, and a sign-valued query check, the acceptance indicator on the dictator queries from that vertex’s label is at most the operational check value for the dictator long-code table plus the check’s arity times the vertex’s local edge error.

**Proof.** Fix a tuple of neighbors, one for each query position. Compare the ideal dictator answers at the vertex with the answers returned through those neighbors. If the ideal predicate rejects, its indicator is zero and the desired pointwise inequality follows from nonnegativity. If it accepts and the actual answers also accept, the inequality follows because every edge-failure indicator is nonnegative. If the ideal accepts but the actual answers reject, at least one position must use a violated edge: otherwise, `FABL.RegularUniqueGame.neighborResponse_dictator_of_satisfied` makes every actual answer equal its ideal answer, forcing acceptance. That failed position contributes $1$ to the sum of failures, while all other terms are nonnegative, so the sum of failures is at least $1$ and covers the ideal indicator. Thus, pointwise, the ideal indicator is bounded by the actual acceptance indicator plus the sum of the positionwise failures. Average over the independent uniform neighbor choices; monotonicity and linearity of finite expectation preserve the inequality (`FABL.pmfExpectation_mono`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_sum`). Independence makes each position’s expected failure its single-coordinate expectation (`FABL.pmfExpectation_independentProductPMF_coordinate`), which under the uniform neighbor law is the local edge error. Summing over the check’s arity gives the claimed error term (`FABL.pmfExpectation_uniformPMF_eq_expect`).

**Key facts.** `FABL.RegularUniqueGame.neighborResponse_dictator_of_satisfied`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_independentProductPMF_coordinate`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
