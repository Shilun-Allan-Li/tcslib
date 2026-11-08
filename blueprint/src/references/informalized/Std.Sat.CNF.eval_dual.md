<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/DNF.lean :: Std.Sat.CNF.eval_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the dual formula

**Claim.** For every CNF formula $\varphi$ and Boolean assignment $a$, the DNF De Morgan dual of $\varphi$ evaluates to the Boolean negation of the evaluation of $\varphi$ under $a$.

**Proof.** First consider a clause $C$. Its dual clause keeps each variable and reverses each literal's Boolean sign. The dual clause is satisfied exactly when at least one literal of $C$ is false, which is precisely when $C$ is not satisfied. This can be checked for each literal's two possible signs, and the clause-level equivalence follows by induction over its literals, including the empty clause. Now induct on the list of clauses in $\varphi$. The DNF dual evaluates as the disjunction of the evaluations of the dual clauses, while the CNF evaluates as the conjunction of the original clause evaluations. For the first clause, the clause-level equivalence identifies its dual evaluation with its negated original evaluation; the induction hypothesis does the same for the remaining clauses. The Boolean identity $\neg(P\land Q)=\neg P\lor\neg Q$ then gives the claimed equality.
