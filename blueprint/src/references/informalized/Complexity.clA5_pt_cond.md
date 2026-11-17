<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5_pt_cond -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Conditional Function

**Claim.** If the Boolean test $x\mapsto[p(x)]$ and the functions $f,g$ are polynomial-time computable, then the function returning $f(x)$ when $p(x)$ is true and $g(x)$ otherwise is polynomial-time computable.

**Proof.** Take machines and polynomial bounds for the test and the two branch functions, say $A(n+1)^a$, $B(n+1)^b$, and $C(n+1)^c$. The machine-level conditional construction (`computesFunInTime_cond`) combines them into a machine whose time is bounded by a constant $K$ times the test time plus the larger branch time plus one. Let $e=\max(a,b,c)$. Since $n+1\ge1$, each of the three bounds is at most its coefficient times $(n+1)^e$, and $1\le(n+1)^e$. Thus the combined bound is at most $K(A+B+C+1)(n+1)^e$. Finally, time computability persists when the allowed time bound is increased (`ComputesInTime.mono`), giving the required polynomial-time computation.

**Key facts.** `Turing.FinTM.computesFunInTime_cond`, `Turing.FinTM.ComputesInTime.mono`.
