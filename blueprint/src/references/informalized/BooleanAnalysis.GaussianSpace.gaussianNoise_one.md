<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian noise at full correlation

**Claim.** For every function $f:\mathbb R^n\to\mathbb R$, Gaussian noise of correlation $1$ leaves $f$ unchanged.

**Proof.** At correlation $1$, the noise coefficient is $\sqrt{1-1^2}=0$, while the coefficient of $x$ is $1$. Hence the integrand defining the noise operator is the constant function of the Gaussian variable with value $f(x)$. The standard Gaussian measure is a probability measure, so integrating this constant returns $f(x)$. This holds for every $x$, giving equality of the functions.
