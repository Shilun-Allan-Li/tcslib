<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.liftOriginalClause_eval_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a lifted original clause

**Claim.** The lifted clause evaluates to $-1$ on the assignment extending the original assignment by the auxiliary coordinates exactly when the original clause evaluates to $-1$.

**Proof.** The evaluation lemma for lifted clauses says that evaluating the lift on an assignment is equivalent to evaluating the original clause on the restriction of that assignment to the original coordinates (`FABL.liftLocalClause_eval_eq_neg_one_iff`). It remains to identify that restriction. Every coordinate of the original assignment has the form obtained by including an index from the first summand of the decomposition into original and auxiliary coordinates. The prefix embedding sends this coordinate to the same original position, and the extended assignment there agrees with the original assignment (`FABL.localPrefixEmbedding_castAdd`, `FABL.extendCNFAssignment_castAdd`). Thus the restriction of the extended assignment is the original assignment, and substitution gives the stated equivalence.

**Key facts.** `FABL.liftLocalClause_eval_eq_neg_one_iff`, `FABL.localPrefixEmbedding_castAdd`, `FABL.extendCNFAssignment_castAdd`.
