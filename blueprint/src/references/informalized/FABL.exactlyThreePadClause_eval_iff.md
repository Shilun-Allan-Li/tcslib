<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.exactlyThreePadClause_eval_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Evaluation of padded clauses

**Claim.** For a clause of width at most three with distinct variable indices, every clause in its specified padding evaluates to $-1$ under an extended assignment exactly when the original clause evaluates to $-1$ under the assignment restricted to the original variables.

**Proof.** Use the fact that a clause evaluates to $-1$ precisely when at least one of its literals is satisfied, meaning the assignment gives that literal's required sign (`FABL.CNFFormula.clauseEval_eq_neg_one_iff`). The proof splits according to the number of literals. For an empty clause, it checks all eight possible sign assignments to the three padding variables against the eight padded clauses: together they are unsatisfied in every assignment, as is the empty original clause. For a one-literal clause, it checks the four possibilities for the first two padding signs; the padded clauses are all unsatisfied exactly when the lifted original literal is unsatisfied. For a two-literal clause, the two padded clauses use opposite required signs at the first padding coordinate, so one is satisfied regardless of that coordinate; hence they are not all unsatisfied, matching the fact that the original disjunction of two literals cannot be unsatisfied in the sense of this evaluation unless both literals are satisfied. For three literals, there is no padding, and lifting the indices preserves the original coordinates, so the clause evaluation agrees directly with the restricted assignment. Finally, four or more literals contradict the width bound, so that case cannot occur.

**Key facts.** `FABL.CNFFormula.clauseEval_eq_neg_one_iff`.

**Caveat.** The stated one- and two-literal behavior appears opposite to the supplied evaluation definition: `clauseEval = -1` means some literal is satisfied, whereas the padding equivalence as stated says all padded clauses have evaluation $-1$ exactly when the original does. The proof's finite case checks are not adequately reconciled with this convention; the informal statement or encoding may be inconsistent.
