<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Density.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_exponent_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian exponent identity

**Claim.** For $\rho,s\in\mathbb R$ with $s\ne0$ and vectors $x,y\in\mathbb R^n$, the sum of the scaled negative squares $(\rho y_i-x_i)^2$ equals the negative half of the sum of the squares of $x_i/s-\rho y_i/s$.

**Proof.** For each coordinate, $-((1/s)x_i+(-\rho/s)y_i)^2/2=-(\rho y_i-x_i)^2/(2s^2)$: rewrite the expression inside the square as $(x_i-\rho y_i)/s$ and use that squaring removes the sign. Summing these coordinatewise equalities gives the identity; distributing the common factor $-1/2$ across the finite sum yields the displayed right-hand side.
