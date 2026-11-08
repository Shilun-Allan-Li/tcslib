<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.gateRelations_of_toWidthThreeCNF_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfying Assignments Enforce Gate Relations

**Claim.** If an assignment makes the circuit's width-three CNF evaluate to $-1$, then it satisfies the relation prescribed at every gate.

**Proof.** A CNF evaluates to $-1$ exactly when every clause in it evaluates to $-1$ (`FABL.CNFFormula.eval_eq_neg_one_iff`). Fix a gate. Its gate relation is equivalent to the condition that every clause in that gate's clause list evaluates to $-1$ (`FABL.BooleanCircuit.gateClauses_eval_iff`). Each such clause occurs in the circuit's width-three CNF: that formula is formed by appending the flattened gate-clause lists and the output clause, so the selected gate's clauses occur in the flattened gate-clause part. Hence every clause required for this gate evaluates to $-1$, and its gate relation follows.

**Key facts.** `FABL.CNFFormula.eval_eq_neg_one_iff`, `FABL.BooleanCircuit.gateClauses_eval_iff`.
