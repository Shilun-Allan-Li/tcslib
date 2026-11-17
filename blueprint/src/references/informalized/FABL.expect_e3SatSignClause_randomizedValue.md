<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.expect_e3SatSignClause_randomizedValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Randomized Value of Replacement Clauses

**Claim.** The average randomized acceptance value over the four replacement clauses is $3/4$ plus one quarter of the randomized acceptance value of the corresponding three-variable linear predicate.

**Proof.** First interchange the average over clauses with the probability-weighted average over input triples; finite averages allow this reordering (\texttt{fintypeExpectation\_pmfExpectation\_comm}). Fix an input triple. Among its four replacement clauses, the sum of the acceptance indicators is three plus the indicator that the triple satisfies the linear predicate (\texttt{sum\_e3SatSignReplacementClauses}). Dividing by four, the clause average at that triple is therefore $3/4$ plus one quarter of the predicate's acceptance indicator. Average this identity over the input distribution. Linearity of the probability-weighted average and the fact that the average of a constant is that constant (\texttt{pmfExpectation\_add}, \texttt{pmfExpectation\_const}, and \texttt{pmfExpectation\_const\_mul}) give the claimed formula.

**Key facts.** `FABL.fintypeExpectation_pmfExpectation_comm`, `FABL.sum_e3SatSignReplacementClauses`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`.
