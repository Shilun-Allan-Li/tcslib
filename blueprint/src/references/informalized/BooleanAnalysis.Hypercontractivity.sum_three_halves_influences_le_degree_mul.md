<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.sum_three_halves_influences_le_degree_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-halves influence bound

**Claim.** If $f$ has Fourier degree at most $k$, variance at most $1$, and every coordinate influence is at most $\varepsilon$, then $\sum_i\operatorname{Inf}_i[f]^{3/2}\le k\sqrt{\varepsilon}$.

**Proof.** For each coordinate, nonnegativity of its influence allows us to write $\operatorname{Inf}_i[f]^{3/2}=\operatorname{Inf}_i[f]\sqrt{\operatorname{Inf}_i[f]}$. The assumed influence bound and monotonicity of the square root give $\sqrt{\operatorname{Inf}_i[f]}\le\sqrt{\varepsilon}$; multiplying by the nonnegative influence bounds this term by $\sqrt{\varepsilon}\operatorname{Inf}_i[f]$. Summing yields $\sqrt{\varepsilon}I[f]$. By the total-influence degree bound (\texttt{BooleanAnalysis.Hypercontractivity.totalInfluence\_le\_degree\_mul\_variance}), $I[f]\le k\operatorname{Var}(f)\le k$, so the result follows.

**Key facts.** `BooleanAnalysis.influence_nonneg`, `BooleanAnalysis.Hypercontractivity.totalInfluence_le_degree_mul_variance`.
