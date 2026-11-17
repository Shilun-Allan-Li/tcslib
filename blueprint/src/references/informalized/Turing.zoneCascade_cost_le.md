<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneCascade_cost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward Cascade Cost Bound

**Claim.** For every natural number $j$, the sum over $0\le i<j$ of $4(2^{i+1}+i+2)$ is at most $16\cdot 2^j$.

**Proof.** We prove the slightly stronger estimate that the sum through $n-1$, with an additional $16$ added, is at most $16\cdot 2^n$. For $n=0$ the sum is empty, and the assertion is equality. For the induction step, the sum through $n$ is the previous sum plus $4(2^{n+1}+n+2)$. The induction hypothesis bounds the previous sum plus $16$ by $16\cdot2^n$. Also $n+2\le 2^{n+1}$, so the new summand is at most $8\cdot2^{n+1}$. Combining these bounds gives the strengthened estimate at $n+1$, since $16\cdot2^{n+1}=16\cdot2^n+16\cdot2^n$ and the required increment is at most $16\cdot2^n$. Dropping the added nonnegative $16$ and taking $n=j$ proves the claim.
