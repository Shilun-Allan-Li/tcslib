<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean :: integral_exp_mul_sq_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Gaussian exponential-square integral

**Claim.** For a standard Gaussian random variable and any real $s$ with $2s<1$, the expectation of $e^{sY^2}$ is $(1-2s)^{-1/2}$.

**Proof.** Write the Gaussian expectation using its density. Multiplying the density $(\sqrt{2\pi})^{-1}e^{-z^2/2}$ by $e^{sz^2}$ combines the exponentials into $(\sqrt{2\pi})^{-1}e^{-(1/2-s)z^2}$. The condition $2s<1$ makes $1/2-s$ positive, so the Gaussian integral formula evaluates the remaining integral as $\sqrt{\pi/(1/2-s)}$. The resulting expression is $(\sqrt{2\pi})^{-1}\sqrt{\pi/(1/2-s)}$. Since both radicands are positive, simplifying the square roots gives $(1-2s)^{-1/2}$.
