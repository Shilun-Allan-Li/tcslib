<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.gateClauses_eval_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate clauses characterize gate relations

**Claim.** For any assignment, every clause associated with a gate evaluates to $-1$ if and only if the assignment satisfies that gate's Boolean relation.

**Proof.** Split according to the type of gate, using the actual gate at the chosen position in each case. For an input gate, the two clauses enforce that the gate coordinate and the input coordinate encode the same Boolean value. For a constant gate, its single clause forces the gate coordinate to encode the specified constant. For a negation gate, the two clauses enforce opposite values at the gate and source coordinates.

For a conjunction gate, first distinguish whether its two source indices coincide. If they do, the clauses reduce to the one-source relation that the output equals that source; checking the two possible signs for the output and source verifies the equivalence. If the indices differ, check the two possible signs at each of the output and source coordinates. The clauses say that a positive output is forbidden when either source is false, and that a negative output is forbidden when both sources are true. Together these are exactly the conjunction truth table.

For a disjunction gate, again separate coincident from distinct source indices. In the coincident case the clauses reduce to the relation that the output equals the common source. In the distinct case, the clauses forbid a negative output if either source is true, and forbid a positive output when both sources are false. These conditions are exactly the disjunction truth table.

In each case, the interpretation of a clause evaluating to $-1$ is that at least one of its literals has its required sign ($\texttt{clauseEval\_eq\_neg\_one\_iff}$). Applying this to the listed clauses and checking the possible signs yields precisely the corresponding gate relation.

**Key facts.** `FABL.CNFFormula.clauseEval_eq_neg_one_iff`.
