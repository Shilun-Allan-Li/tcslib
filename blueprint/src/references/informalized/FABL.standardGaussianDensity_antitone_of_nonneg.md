<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.standardGaussianDensity_antitone_of_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Density decreases on the nonnegative axis

**Claim.** If $0\le x\le y$, then the standard Gaussian density at $y$ is at most its value at $x$.

**Proof.** The standard Gaussian density is a positive constant times $\exp(-u^2/2)$. Since $0\le x\le y$, squaring preserves the order and gives $x^2\le y^2$. Hence $-y^2/2\le -x^2/2$; monotonicity of the exponential gives $\exp(-y^2/2)\le \exp(-x^2/2)$. Multiplication by the positive normalizing constant proves the claim.
