<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance.lean :: BooleanAnalysis.GaussianSpace.invariance_quarter_power_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth-Root Scale Inequality

**Claim.** For every integer $k\ge0$ and every $\varepsilon\ge0$, $(k9^k\varepsilon)^{1/4}\le2^k\varepsilon^{1/4}$.

**Proof.** The elementary exponential estimate `degree_mul_nine_pow_le_sixteen_pow` gives $k9^k\le16^k$. Multiplying by the nonnegative $\varepsilon$ and using monotonicity of the fourth-root power yields $(k9^k\varepsilon)^{1/4}\le(16^k\varepsilon)^{1/4}$. Since $16^{1/4}=2$, the fourth root of the product factors as $(16^k)^{1/4}\varepsilon^{1/4}=2^k\varepsilon^{1/4}$, proving the inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.degree_mul_nine_pow_le_sixteen_pow`.
