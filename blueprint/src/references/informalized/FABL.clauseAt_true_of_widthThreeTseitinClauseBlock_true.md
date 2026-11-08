<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.clauseAt_true_of_widthThreeTseitinClauseBlock_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction of the Original Clause

**Claim.** If an assignment makes every clause in the width-three Tseitin block for clause $i$ true, then the original clause $i$ is true on the restriction of that assignment to the original variables.

**Proof.** Let the lifted literals be those of clause $i$ with their indices moved into the enlarged variable set, and let the auxiliary literals be those introduced for its Tseitin block. Their indices are respectively distinct, and the lifted indices are disjoint from the auxiliary indices (`FABL.nodupIndices_tseitinLiftLiterals`, `FABL.nodupIndices_tseitinAuxiliaryLiterals`, and `FABL.disjoint_tseitinLiftLiterals_tseitinAuxiliaryLiterals`). Thus the equivalence between satisfaction of the Tseitin clause chain and satisfaction of the corresponding clause terms applies (`FABL.literalListsHold_iff_tseitinClauseTerms`). The hypothesis that every term in the block is true gives satisfaction of that entire chain; the chain property then implies that all lifted original literals hold (`FABL.literalListHolds_of_tseitinClauseChain`). In particular, some original literal in clause $i$ holds after lifting. Unpacking the lift identifies it as an original literal, and restricting the assignment to the original variables preserves its required value. A clause evaluates to true exactly when some literal in it has its required value (`FABL.CNFFormula.clauseEval_eq_neg_one_iff`), so the original clause evaluates to true on the restricted assignment.

**Key facts.** `FABL.nodupIndices_tseitinLiftLiterals`, `FABL.nodupIndices_tseitinAuxiliaryLiterals`, `FABL.disjoint_tseitinLiftLiterals_tseitinAuxiliaryLiterals`, `FABL.literalListsHold_iff_tseitinClauseTerms`, `FABL.literalListHolds_of_tseitinClauseChain`, `FABL.CNFFormula.clauseEval_eq_neg_one_iff`.
