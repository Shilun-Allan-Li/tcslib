<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_loop_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Loop Bound

**Claim.** For all natural numbers $b,A,r,n$, $b\bigl(A(n+1)^{r+1}+1\bigr)(n+2)\le 2b(A+1)(n+1)^{r+2}$.

**Proof.** Since $(n+1)^{r+1}\ge 1$, we have $A(n+1)^{r+1}+1\le (A+1)(n+1)^{r+1}$. Also $n+2\le 2(n+1)$. Multiplying these inequalities by the nonnegative factors gives an upper bound of $b(A+1)(n+1)^{r+1}\cdot 2(n+1)$. Combining the powers yields the claimed right-hand side.
