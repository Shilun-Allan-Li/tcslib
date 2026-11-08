<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.CNFFormula.clauseEval_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterizing a negative clause value

**Claim.** A clause evaluates to $-1$ at an assignment exactly when some literal in the clause has its required sign at its indexed coordinate.

**Proof.** The clause evaluates to $-1$ precisely when at least one of its literals evaluates to $-1$. For an individual literal, its evaluation is $-1$ exactly when the assignment at that literal’s index equals its required sign (the characterization `FABL.Literal.eval_eq_neg_one_iff`). Combining these facts, the clause evaluates to $-1$ exactly when there is a literal in the clause whose indexed coordinate has its required sign.

**Key facts.** `FABL.Literal.eval_eq_neg_one_iff`.
