<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.pmfExpectation_productCoordinateNoisePMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation Under Coordinate Noise

**Claim.** For the mixture that retains $x$ with probability $\rho$ and otherwise samples from $\pi$, the expectation of $f$ is $\rho f(x)+(1-\rho)\mathbb E_{y\sim\pi}[f(y)]$.

**Proof.** Condition on the retain bit in the defining mixture. The expectation over the resulting law is the expectation over the bit of the conditional payoff (`pmfExpectation_bind`). If the bit says retain, the conditional distribution is concentrated at $x$, so its payoff is $f(x)$ (`pmfExpectation_pure`); otherwise the payoff is $\mathbb E_{y\sim\pi}[f(y)]$. Averaging these two payoffs with probabilities $\rho$ and $1-\rho$ gives the formula.

**Key facts.** `FABL.nonnegativeCorrelationProbability_le_one`, `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_pure`.
