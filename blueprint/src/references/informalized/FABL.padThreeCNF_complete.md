<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.padThreeCNF_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfiability under padding

**Claim.** If an assignment to the original and auxiliary variables makes every clause of the given formula evaluate to $-1$, then the assignment extended by filler values makes the padded formula evaluate to $-1$ as well.

**Proof.** The characterization of formula value $-1$ reduces the goal to showing that every clause in the padded formula evaluates to $-1$ (\texttt{CNFFormula.eval\_eq\_neg\_one\_iff}). Each padded clause comes from some index $q<K$. If $q$ is below the original formula size, that clause is a lifted original clause. The lift evaluation equivalence reduces its value to that of the original clause on the restricted assignment (\texttt{liftLocalClause\_eval\_eq\_neg\_one\_iff}); restriction of the extended padded assignment recovers the original extended assignment (\texttt{restrictLocalAssignment\_extend\_pad}). The original clause therefore evaluates to $-1$ by the assumed satisfaction. Otherwise the padded clause is the filler clause. Its first literal requires value $-1$ at auxiliary coordinate $a$, and the filler-coordinate property gives precisely that value (\texttt{padAuxiliaryAssignment\_filler}); hence this clause evaluates to $-1$. These two cases cover every padded clause, proving the claim.

**Key facts.** `FABL.CNFFormula.eval_eq_neg_one_iff`, `FABL.liftLocalClause_eval_eq_neg_one_iff`, `FABL.restrictLocalAssignment_extend_pad`, `FABL.padAuxiliaryAssignment_filler`.
