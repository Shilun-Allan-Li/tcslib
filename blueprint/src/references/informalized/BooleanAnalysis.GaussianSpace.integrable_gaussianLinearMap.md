<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SmoothVariation.lean :: BooleanAnalysis.GaussianSpace.integrable_gaussianLinearMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of Gaussian Linear Functionals

**Claim.** Every continuous real linear functional on $\mathbb R^n$ is integrable under the product standard Gaussian measure.

**Proof.** The identity function on the real line is integrable under the standard Gaussian law, since it belongs to $L^1$ there. Each coordinate projection on $\mathbb R^n$ is measure-preserving from the product Gaussian measure to that one-dimensional law, so each coordinate function is integrable on the product space. A linear functional on the finite-dimensional product space is the finite sum of these coordinate functions multiplied by its coefficients. Finite linear combinations of integrable functions are integrable, which proves the claim.
