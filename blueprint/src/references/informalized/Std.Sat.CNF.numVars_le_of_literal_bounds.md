<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.numVars_le_of_literal_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable count from literal bounds

**Claim.** If every literal $(v,b)$ in every clause of a CNF formula $\varphi$ satisfies $v+1\le n$, then its variable count $N(\varphi)$ is at most $n$.

**Proof.** The variable count is the maximum, with default value zero, of the numbers $v+1$ contributed by the literals in all clauses. First, for any finite list of numbers all bounded above by $n$, its maximum with default zero is at most $n$: induction on the list reduces this to the fact that the maximum of two numbers bounded by $n$ is also bounded by $n$. Every number in the list used to define $N(\varphi)$ comes from some literal in some clause, so the hypothesis bounds it by $n$. Applying the list bound proves $N(\varphi)\le n$.
