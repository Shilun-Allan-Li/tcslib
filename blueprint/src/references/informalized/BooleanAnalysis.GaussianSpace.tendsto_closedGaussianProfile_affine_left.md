<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/TwoPoint.lean :: BooleanAnalysis.GaussianSpace.tendsto_closedGaussianProfile_affine_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the closed Gaussian profile

**Claim.** Under the stated interval hypotheses on $a$ and $a+b$, the closed Gaussian profile at $a+\rho b$ tends to its value at $a+b$ as $\rho$ approaches $1$ from below.

**Proof.** The affine map $\rho\mapsto a+\rho b$ tends to $a+b$ as $\rho\to1$. For $\rho<1$ sufficiently close to $1$, we also have $0<\rho<1$. Then $a+\rho b=\rho(a+b)+(1-\rho)a$ is a convex combination of the two points $a+b$ and $a$, both in $[0,1]$. Thus these affine values remain in the interval on which the closed Gaussian profile is continuous (`continuousOn_closedGaussianProfile`). Composing that continuity with the affine convergence, restricted to the left-hand neighborhood of $1$, gives the claimed limit.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuousOn_closedGaussianProfile`.
