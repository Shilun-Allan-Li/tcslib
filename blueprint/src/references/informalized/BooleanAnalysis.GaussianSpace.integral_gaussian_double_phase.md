<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.integral_gaussian_double_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Double Gaussian phase integral

**Claim.** The iterated Gaussian integral of the two complex phases times $f$ equals the complexification of the stated real Gaussian integral with the exponential weight.

**Proof.** First move the outer phase inside the inner integral as a constant factor. The resulting double integral may be swapped by Fubini: the integrand is integrable on the product Gaussian space, as established by `integrable_gaussian_double_phase`. For fixed $y$, combine the two phases using the phase multiplication identity (`gaussianPhase_mul`); the inner integral over $t$ is then the Gaussian characteristic-function integral (`integral_exp_mul_I_gaussianPi`), equal to $\exp(-\sum_i(a x_i+b y_i)^2/2)$. This leaves the integral of that exponential times $f(y)$ as a complex-valued integral. Since the exponential weight and $f$ are real-valued, identify this integral with the complexification of the corresponding real integral.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_gaussian_double_phase`, `BooleanAnalysis.GaussianSpace.gaussianPhase_mul`, `BooleanAnalysis.GaussianSpace.integral_exp_mul_I_gaussianPi`.
