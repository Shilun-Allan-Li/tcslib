<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNF.lean :: Complexity.falsifyingClause_eval_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# When an Excluding Clause Is False

**Claim.** The clause excluding a vector $v$ evaluates to false under an assignment exactly when the assignment agrees with $v$ at every position below $\ell$.

**Proof.** The clause contains, for each position $i<\ell$, the literal that is false precisely when the assigned bit at $i$ equals $v_i$. A disjunction is false exactly when every one of its literals is false. Therefore the clause is false exactly when the assignment agrees with $v$ at every position.
