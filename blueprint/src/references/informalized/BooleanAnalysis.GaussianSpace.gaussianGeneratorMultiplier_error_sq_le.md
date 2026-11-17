<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Generator.lean :: BooleanAnalysis.GaussianSpace.gaussianGeneratorMultiplier_error_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Multiplier Error Bound

**Claim.** For every $d\ge0$, $t>0$, and real $c$, the squared multiplier error obeys $((m_d(t)-d)c)^2\le (dc)^2$.

**Proof.** The multiplier bounds give $0\le m_d(t)\le d$. Consequently its difference from $d$ lies between $-d$ and $0$, so $(m_d(t)-d)^2\le d^2$. Multiplying this inequality by the nonnegative number $c^2$ yields the asserted bound after regrouping the squares (`gaussianGeneratorMultiplier_bounds`).

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianGeneratorMultiplier_bounds`.
