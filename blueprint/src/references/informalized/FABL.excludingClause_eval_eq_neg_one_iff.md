<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.excludingClause_eval_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of an excluding clause

**Claim.** The clause constructed to exclude a sign assignment evaluates to $-1$ at another assignment exactly when that other assignment differs from the excluded one.

**Proof.** The clause evaluates to $-1$ exactly when some literal in it has its required sign at the input (\texttt{CNFFormula.clauseEval\_eq\_neg\_one\_iff}). The constructed clause has, for each coordinate $i$, a literal requiring the sign opposite to the excluded assignment at $i$. If the input equals the excluded assignment, none of these literals has its required sign, so the clause cannot evaluate to $-1$. Conversely, if the input differs from the excluded assignment, some coordinate $i$ differs. Since both coordinate values are signs, the input's value there is the opposite of the excluded value. The literal for coordinate $i$ therefore has its required sign at the input, and the clause evaluates to $-1$.

**Key facts.** `FABL.CNFFormula.clauseEval_eq_neg_one_iff`.
