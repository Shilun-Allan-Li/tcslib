<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourProgram_work_polynomial_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial local-work bound

**Claim.** Every output and cost pair in the support of the Kushilevitz–Mansour program has local work at most $2^{42}(n+1)^3(M+1)^8/\varepsilon^{10}$.

**Proof.** Put $\tau=\varepsilon/(4M)$. The full-program work bound is the sum of the Goldreich–Levin work budget and the second-stage contribution $1280A^4(n+1)/\varepsilon^2$, where $A$ is the active-set cap (\texttt{kushilevitzMansourProgram\_work\_cast\_le}). The Goldreich–Levin budget is at most $2^{25}n(n+1)^2/\tau^8$, while $A\le8/\tau^2$ (\texttt{goldreichLevinWorkBudget\_cast\_le}, \texttt{goldreichLevinActiveCap\_cast\_le}). Substitution of $\tau=\varepsilon/(4M)$ bounds the first term by $2^{41}n(n+1)^2M^8/\varepsilon^8$. Because $n\le n+1$, $\varepsilon^2\le1$, $M^8\le(M+1)^8$, and $n+1\le(n+1)^3$, this is at most $2^{41}(n+1)^3(M+1)^8/\varepsilon^{10}$. For the second term, the cap estimate gives $1280(8/\tau^2)^4(n+1)/\varepsilon^2=343597383680(n+1)M^8/\varepsilon^{10}$. Here $n+1\le(n+1)^3$, $M^8\le(M+1)^8$, and $343597383680\le2^{41}$, so it has the same upper bound. Adding the two estimates yields $2^{42}(n+1)^3(M+1)^8/\varepsilon^{10}$.

**Key facts.** `FABL.kushilevitzMansourProgram_work_cast_le`, `FABL.goldreichLevinWorkBudget_cast_le`, `FABL.goldreichLevinActiveCap_cast_le`.
