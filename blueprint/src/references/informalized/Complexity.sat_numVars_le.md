<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_numVars_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the CNF Variable Count

**Claim.** If every literal in every clause of $\varphi$ has variable index less than $n$, then the variable count of $\varphi$ is at most $n$.

**Proof.** The variable count is the maximum, with $0$ as the initial value, of the numbers $\ell.1+1$ arising from literals in the flattened formula. Each such number comes from a clause $C$ of $\varphi$ and a literal $\ell$ in $C$. The hypothesis gives $\ell.1<n$, so $\ell.1+1\le n$. Thus every entry being maximized is at most $n$; consequently their maximum, including the initial value $0$, is at most $n.
