<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourProgram_queries_polynomial_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership-query polynomial bound

**Claim.** For every output and cost pair in the support of the Kushilevitz–Mansour program, the membership-query count is at most $2^{40}(n+1)^2(M+1)^8/\varepsilon^{10}$.

**Proof.** Set $\tau=\varepsilon/(4M)$. The query accounting theorem for the full program bounds its query count by the sum of the Goldreich–Levin stage budget and the second-stage estimator budget (\texttt{kushilevitzMansourProgram\_queries\_cast\_le}). The Goldreich–Levin query budget is at most $2^{21}n(n+1)/\tau^8$, and its active-set cap is at most $8/\tau^2$ (\texttt{goldreichLevinQueryBudget\_cast\_le}, \texttt{goldreichLevinActiveCap\_cast\_le}). Substituting $\tau=\varepsilon/(4M)$, the first contribution becomes $2^{37}n(n+1)M^8/\varepsilon^8$. Since $n\le n+1$, $M^8\le(M+1)^8$, and $\varepsilon^2\le1$, this is at most $2^{39}(n+1)^2(M+1)^8/\varepsilon^{10}$. The second contribution, $640A^4/\varepsilon^2$ with $A$ the active-set cap, is at most $640(8/\tau^2)^4/\varepsilon^2=171798691840M^8/\varepsilon^{10}$. Using $(n+1)^2\ge1$, $(M+1)^8\ge M^8$, and $171798691840\le2^{39}$, it too is bounded by $2^{39}(n+1)^2(M+1)^8/\varepsilon^{10}$. Adding the two estimates gives the claimed bound.

**Key facts.** `FABL.kushilevitzMansourProgram_queries_cast_le`, `FABL.goldreichLevinQueryBudget_cast_le`, `FABL.goldreichLevinActiveCap_cast_le`.
