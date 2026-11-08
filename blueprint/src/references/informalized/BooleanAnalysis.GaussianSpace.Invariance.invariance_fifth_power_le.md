<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceDistribution.lean :: BooleanAnalysis.GaussianSpace.Invariance.invariance_fifth_power_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fifth-Root Power Inequality

**Claim.** For every natural number $k$ and real number $\varepsilon\ge0$, the stated fifth-root expression is at most $2^k\varepsilon^{1/5}$.

**Proof.** The degree estimate $k9^k\le16^k$ (`degree_mul_nine_pow_le_sixteen_pow`) and $16\le32$ give $k9^k\le32^k$. After dividing by $12$ and multiplying by $\varepsilon\ge0$, the quantity inside the left fifth root is at most $32^k\varepsilon$. Taking the increasing fifth-root power preserves the inequality. By the product rule for nonnegative real powers, $(32^k\varepsilon)^{1/5}=(32^k)^{1/5}\varepsilon^{1/5}$. Since $32=2^5$, the first factor is $2^k$, proving the result, also when $\varepsilon=0$.

**Key facts.** `BooleanAnalysis.GaussianSpace.degree_mul_nine_pow_le_sixteen_pow`.
