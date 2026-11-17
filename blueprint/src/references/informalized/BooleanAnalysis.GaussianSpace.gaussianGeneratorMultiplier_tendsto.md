<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Generator.lean :: BooleanAnalysis.GaussianSpace.gaussianGeneratorMultiplier_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Generator multiplier limit

**Claim.** For every integer $d\ge 0$, the Gaussian generator multiplier $m_d(t)$ tends to $d$ as $t$ tends to $0$ through positive values.

**Proof.** Consider $F(t)=1-(e^{-t})^d$. By the chain rule, the derivative of $e^{-t}$ at $0$ is $-1$, and the power rule gives $F'(0)=d$. Since $F(0)=0$, the quotient $F(t)/t$ is the slope of $F$ from $0$ to $t$. The theorem that slopes converge to the derivative at the base point therefore gives the asserted limit, also when the domain approaches $0$ from the right.
