<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.liftLocalClause_eval_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a lifted clause

**Claim.** For $a\le K$, a clause on $r+a$ sign coordinates with distinct literal coordinates evaluates to $-1$ on an assignment to $r+K$ coordinates exactly when the original clause evaluates to $-1$ on the restricted assignment.

**Proof.** A clause evaluates to $-1$ exactly when at least one of its literals has its required sign on the assignment (\(\mathrm{FABL.CNFFormula.clauseEval\_eq\_neg\_one\_iff}\)). If a lifted clause evaluates to $-1$, choose such a lifted literal. By the definition of lifting, it comes from an original literal in the clause; its coordinate is the image of the original coordinate and its required sign is unchanged. The restricted assignment reads the larger assignment at precisely that image coordinate, so the original literal also has its required sign. Conversely, if an original literal witnesses value $-1$ for the original clause on the restricted assignment, its lift is a literal of the lifted clause. The same coordinate identity and unchanged required sign show that this lifted literal is satisfied by the larger assignment. Thus each direction preserves the witnessing literal.

**Key facts.** `FABL.CNFFormula.clauseEval_eq_neg_one_iff`.
