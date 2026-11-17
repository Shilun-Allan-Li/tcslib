<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.F₂DecisionTree.eval_toCNFFormula_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CNF Evaluation and Satisfying Paths

**Claim.** The CNF formula associated to a decision tree evaluates to $1$ at an input exactly when there is a path ending at output $1$ whose queried-coordinate assignments match that input.

**Proof.** If the CNF evaluates to $1$, not all of its clauses evaluate to $-1$, since the formula is defined to be $-1$ precisely when every clause does. Thus some clause does not evaluate to $-1$. Each clause is a path clause coming from a path with output $1$; since its value is a sign, not being $-1$ means it is $1$. The path-clause equivalence (`FABL.F₂DecisionTree.Path.clauseEval_toCNFClause_eq_one_iff`) says that this clause evaluates to $1$ exactly when the path assignments match the input, giving the required path. Conversely, suppose such a matching path with output $1$ is given. Its clause belongs to the formula and, by the same equivalence, evaluates to $1$. If the whole CNF evaluated to $-1$, every clause would evaluate to $-1$, contradicting this clause’s value. Hence the formula evaluates to $1$.

**Key facts.** `FABL.F₂DecisionTree.Path.clauseEval_toCNFClause_eq_one_iff`.
