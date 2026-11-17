<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.sum_sq_influences_le_degree_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared influence bound

**Claim.** If $f$ has Fourier degree at most $k$, variance at most $1$, and each coordinate influence is at most $\varepsilon$ with $\varepsilon\ge0$, then the sum of squared coordinate influences is at most $k\varepsilon$.

**Proof.** For each coordinate $i$, nonnegativity of its influence and the bound $\operatorname{Inf}_i[f]\le\varepsilon$ imply $\operatorname{Inf}_i[f]^2\le\varepsilon\operatorname{Inf}_i[f]$. Summing gives an upper bound of $\varepsilon I[f]$, where $I[f]$ is the total influence. The degree bound on total influence (\texttt{BooleanAnalysis.Hypercontractivity.totalInfluence\_le\_degree\_mul\_variance}) gives $I[f]\le k\operatorname{Var}(f)$. Since $k\ge0$ and $\operatorname{Var}(f)\le1$, this is at most $k$, and multiplying by the nonnegative $\varepsilon$ yields the claimed inequality.

**Key facts.** `BooleanAnalysis.influence_nonneg`, `BooleanAnalysis.Hypercontractivity.totalInfluence_le_degree_mul_variance`.
