<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.global_matches_local -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Global and local clause agreement

**Claim.** For any 3-clause produced by encoding the clause at index $i$, satisfaction under the global assignment is equivalent to satisfaction under the corresponding local assignment.

**Proof.** Each of the three literals of a produced clause is local to its clause index (`SATTo3SAT.transformClause_isLocal`). Apply the agreement of global and local assignments on local literals (`SATTo3SAT.eval_local_eq_global`) separately to the three literals. A 3-clause is satisfied precisely when at least one of these three literals is true; replacing each truth value by its equal value under the other assignment leaves this disjunction unchanged. Hence the satisfaction statements are equivalent.

**Key facts.** `SATTo3SAT.transformClause_isLocal`, `SATTo3SAT.eval_local_eq_global`.
