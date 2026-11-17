<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_poly_cond -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Conditional Branching

**Claim.** If the Boolean test output as a one-bit word and each of $f$ and $g$ are polynomial-time computable, then the function returning $f(x)$ when $p(x)$ is true and $g(x)$ otherwise is polynomial-time computable.

**Proof.** Choose machines for the test and for $f,g$, with time bounds $A(n+1)^a$, $B(n+1)^b$, and $C(n+1)^c$, respectively. The machine-combination result for conditional computation (Turing.FinTM.computesFunInTime_cond) gives a machine for the desired branch with a bound of the form $K\bigl(A(n+1)^a+\max(B(n+1)^b,C(n+1)^c)+1\bigr)$, for some constant $K$. Let $e=\max(a,b,c)$. Since $n+1\ge1$, each power with exponent $a,b,$ or $c$ is at most $(n+1)^e$. The maximum of the two branch bounds is at most their sum, and $1\le(n+1)^e$. Thus the combined time is at most $K(A+B+C+1)(n+1)^e$, a polynomial-time bound. The machine's computation at this larger bound follows from monotonicity of computation time (Turing.FinTM.ComputesInTime.mono).

**Key facts.** `Turing.FinTM.computesFunInTime_cond`, `Turing.FinTM.ComputesInTime.mono`.
