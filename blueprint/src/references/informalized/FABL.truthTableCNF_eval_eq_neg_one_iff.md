<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.truthTableCNF_eval_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth-Table CNF Evaluation

**Claim.** The truth-table CNF evaluates to $-1$ at an assignment exactly when the predicate evaluates to $-1$ there.

**Proof.** A CNF evaluates to $-1$ precisely when every clause evaluates to $-1$ (`CNFFormula.eval_eq_neg_one_iff`). For the forward implication, suppose every clause is false and the predicate at the given assignment were $+1$. The clause excluding that very assignment is then included in the formula, but it evaluates to $-1$ exactly at assignments different from the one it excludes (`excludingClause_eval_eq_neg_one_iff`), a contradiction. Since the predicate takes values in $\{\pm1\}$, it must therefore be $-1$. Conversely, suppose the predicate at the given assignment is $-1$. Every clause in the formula excludes some assignment where the predicate is $+1$. That excluded assignment cannot equal the given one, so the clause is false there by the excluding-clause characterization. Thus every clause is false, and the CNF evaluates to $-1$.

**Key facts.** `FABL.CNFFormula.eval_eq_neg_one_iff`, `FABL.excludingClause_eval_eq_neg_one_iff`.
