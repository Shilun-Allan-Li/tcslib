<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.stableInfluence_le_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence Is at Most Influence

**Claim.** For $\rho\in[0,1]$, every real-valued function on the sign cube, and every coordinate $i$, stable influence at parameter $\rho$ is at most ordinary influence.

**Proof.** Write ordinary influence as the sum $\sum_{S\ni i}\widehat f(S)^2$ (`influence_eq_sum_sq_fourierCoeff`). In the stable-influence sum, each such squared coefficient is multiplied by $\rho^{|S|-1}$. Because $0\leq\rho\leq1$, this factor is at most $1$. Each squared coefficient is nonnegative, so termwise comparison of the finite sums proves the inequality.

**Key facts.** `FABL.influence_eq_sum_sq_fourierCoeff`.
