<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.integral_gaussianNoise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian noise preserves expectation

**Claim.** For $\rho\in[-1,1]$ and integrable $f$, the integral of its Gaussian noise average under product standard Gaussian measure equals the integral of $f$ under that measure.

**Proof.** Define $E(x,w)=\rho x+\sqrt{1-\rho^2}\,w$ coordinatewise. The endpoint-preservation result (\texttt{measurePreserving_gaussianEndpoint}) says that $E$ sends the product of two standard Gaussian measures to the standard Gaussian measure. Fubini's theorem first identifies the integral of the noise average with the product-space integral of $f(E(x,w))$. The change of variables formula for the measure-preserving map $E$ then identifies that integral with the integral of $f$ under the standard Gaussian measure.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianEndpoint`.
