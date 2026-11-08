<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InputMoments.lean :: BooleanAnalysis.GaussianSpace.integral_uniformBool_pi_eq_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Cube Integration Formula

**Claim.** For every $n\ge 0$ and every function $f:\{0,1\}^n\to\mathbb R$, integration against the product of uniform measures on the two-point space equals the uniform cube expectation.

**Proof.** Each point of the two-point space has mass $1/2$. By the product measure formula, every singleton cube point therefore has mass $2^{-n}$; equivalently, its mass as a real number is the uniform weight. The finite-space moment formula identifies the first moment of $f$ under any probability measure assigning this same mass to every point with the uniform cube expectation (the fact `moment_eq_expect`). Apply it to the product measure and the first moment. Since the first moment is the integral of $f$, this gives the stated identity.

**Key facts.** `BooleanAnalysis.moment_eq_expect`.
