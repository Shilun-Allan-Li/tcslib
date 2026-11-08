<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.composeThreeQueryVerifier_accepts_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Matches Clause Evaluation

**Claim.** For any word and composed-verifier seed $(s,q)$, the composed verifier accepts exactly when the clause indexed by $q$ for $s$ evaluates to $-1$ on the sign assignment induced by the word at the composition addresses.

**Proof.** The clause evaluates to $-1$ exactly when some literal in it has its indexed sign equal to that literal's required sign (`CNFFormula.clauseEval_eq_neg_one_iff`). The composed verifier's transcript at each of its three query positions consists of the word's value at the corresponding composition literal address: its queries are defined to be those addresses, and the transcript applies the word to each query (`NonadaptiveFunctionTester.transcript_apply`). Thus verifier acceptance says that at least one of the three listed literal positions has the required sign. Each listed position gives a literal in the clause, so this implies the clause condition. Conversely, any literal in the clause is represented by one of the three positions (`SeedwiseThreeCNFReduction.mem_clause_iff_exists_literal`); its required-sign condition therefore gives an accepting position. The sign read at that address is precisely the coordinate of the composition-induced assignment, proving the equivalence.

**Key facts.** `FABL.CNFFormula.clauseEval_eq_neg_one_iff`, `FABL.NonadaptiveFunctionTester.transcript_apply`, `FABL.SeedwiseThreeCNFReduction.mem_clause_iff_exists_literal`.
