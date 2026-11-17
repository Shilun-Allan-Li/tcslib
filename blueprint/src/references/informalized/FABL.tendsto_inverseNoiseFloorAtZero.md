<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.tendsto_inverseNoiseFloorAtZero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse Noise Floor Divergence

**Claim.** As the noise parameter tends to zero through positive values, its inverse noise floor tends to infinity.

**Proof.** Fix a natural number $N$. Because the coordinate map from the half interval to the reals is continuous, all parameters sufficiently close to zero satisfy $\delta<1/(N+1)$. Restrict to positive such parameters. Multiplying this inequality by $N+1$ gives $\delta(N+1)<1$. Since $N<N+1$, it follows that $N\delta<1$, and hence $N\le 1/\delta$. The inverse noise floor is the natural floor of $1/\delta$, so the defining property of the floor gives $N\le N(\delta)$. This holds for every $N$ throughout a sufficiently small positive neighborhood of zero, which is precisely divergence to infinity.
