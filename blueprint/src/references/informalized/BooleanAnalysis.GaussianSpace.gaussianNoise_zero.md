<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian noise at zero

**Claim.** At correlation parameter $0$, the Gaussian noise operator is the constant function whose value is the Gaussian integral of $f$.

**Proof.** Fix an input point $x$. By definition, $(T_0f)(x)$ is the integral over $y$ of $f$ evaluated at the vector with coordinates $0\cdot x_i+\sqrt{1-0^2}\,y_i$. Each coordinate simplifies to $y_i$, so the integrand is just $f(y)$. Thus the value is $\int f\,d\gamma$, independently of $x$, which proves equality of the two functions.
