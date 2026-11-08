<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Generator.lean :: BooleanAnalysis.GaussianSpace.gaussianGeneratorMultiplier_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for the Generator Multiplier

**Claim.** For every nonnegative integer $d$ and every $t>0$, the Gaussian generator multiplier satisfies $0\le m_d(t)\le d$.

**Proof.** By the definition of the multiplier and the identity $(e^{-t})^d=e^{-dt}$, it is $(1-e^{-dt})/t$. Since $dt\ge0$, the exponential is at most $1$, so the numerator is nonnegative and division by positive $t$ gives the lower bound. For the upper bound, the exponential inequality $1+u\le e^u$ applied to $u=-dt$ gives $1-dt\le e^{-dt}$, hence $1-e^{-dt}\le dt$. Divide by $t>0$ to obtain $m_d(t)\le d$.
