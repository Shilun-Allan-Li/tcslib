<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean :: integral_exp_mul_sq_gaussianReal_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian quadratic exponential integral

**Claim.** For $v>0$ and $2tv<1$, the integral of $e^{ty^2}$ against the centered Gaussian of variance $v$ equals $1/\sqrt{1-2tv}$.

**Proof.** The centered Gaussian of variance $v$ is the distribution of $\sqrt v\,Z$, where $Z$ is standard normal. Changing variables through this scaling reduces the integral to the standard Gaussian integral of $e^{(tv)z^2}$. The condition $2tv<1$ is exactly the convergence condition for that integral. Applying the standard Gaussian quadratic-exponential formula (integral_exp_mul_sq_standardGaussian) gives $1/\sqrt{1-2tv}$, as required.

**Key facts.** `integral_exp_mul_sq_standardGaussian`.
