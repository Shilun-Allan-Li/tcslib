<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_ite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computable Branching

**Claim.** If the predicate $p$, represented by the one-bit output $[p(x)]$, and the two functions $f$ and $g$ are polynomial-time computable, then the function returning $f(x)$ when $p(x)$ is true and $g(x)$ otherwise is polynomial-time computable.

**Proof.** Take polynomial-time machines for the predicate and the two branches. The machine construction for conditional computation combines them into a machine that computes the selected branch, with time bounded by $K(T_0(n)+\max(T_1(n),T_2(n))+1)$ for some constant $K$, where each $T_j$ is the corresponding input time bound (`FinTM.computesFunInTime_cond`). Write these bounds as $A(n+1)^a$, $B(n+1)^b$, and $C(n+1)^c$. Set $e=\max(a,\max(b,c))$. Since $n+1\ge1$, each power with exponent $a,b,$ or $c$ is at most $(n+1)^e$. Also, the maximum of the two branch bounds is at most their sum, and $1\le(n+1)^e$. Consequently the conditional machine's time is at most $K(A+B+C+1)(n+1)^e$. This is a polynomial bound; increasing the time bound preserves the computation (`ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.computesFunInTime_cond`, `Turing.FinTM.ComputesInTime.mono`.
