<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.padThreeCNF_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of padded formulas

**Claim.** If the padded formula evaluates to $-1$ on an assignment to the original variables and the $K$ auxiliary coordinates, then the original formula evaluates to $-1$ on the original variables together with the first $a$ auxiliary values.

**Proof.** Use the characterization of formula value $-1$ to fix any original clause and show that it evaluates to $-1$ (\texttt{CNFFormula.eval\_eq\_neg\_one\_iff}). Choose an occurrence of that clause in the original clause list, and let its position be $i$. Because the original formula has at most $K$ clauses, this position also indexes the padded list. At that position the padded construction takes the lifted original clause, so the padded formula's assumed value implies that this lifted clause evaluates to $-1$. The lift evaluation equivalence converts this to evaluation of the original clause on the restricted assignment (\texttt{liftLocalClause\_eval\_eq\_neg\_one\_iff}). Restricting the assignment formed from the original variables and all $K$ auxiliary values gives the original variables together with the prefix of $a$ auxiliary values (\texttt{restrictLocalAssignment\_extend\_prefix}). Thus the chosen original clause, and hence every original clause, evaluates to $-1$.

**Key facts.** `FABL.CNFFormula.eval_eq_neg_one_iff`, `FABL.liftLocalClause_eval_eq_neg_one_iff`, `FABL.restrictLocalAssignment_extend_prefix`.
