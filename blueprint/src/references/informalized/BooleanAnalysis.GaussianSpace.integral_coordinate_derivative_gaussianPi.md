<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Integration.lean :: BooleanAnalysis.GaussianSpace.integral_coordinate_derivative_gaussianPi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Coordinate Integration by Parts

**Claim.** For the standard Gaussian product measure on $\mathbb R^n$, if $u$ and its coordinate derivative $v$ satisfy the stated differentiability and integrability hypotheses, then $\int v\,d\gamma_n=\int x_i u(x)\,d\gamma_n(x)$.

**Proof.** If $n=0$, there is no coordinate $i$, so the assertion has no instances. For $n>0$, reorder the coordinates so that coordinate $i$ is first. This coordinate permutation preserves the product Gaussian measure and carries the assumed integrability of $u$, $v$, and $x_i u$ to the reordered functions. Fubini's theorem then reduces the two integrals to iterated integrals: for almost every fixed choice of the other coordinates, integrate in the first coordinate. Along that one-dimensional slice, the derivative of $u$ is $v$, by the assumed derivative relation. The one-dimensional Gaussian integration-by-parts identity (`integral_derivative_standardGaussian`) says that the integral of this derivative equals the integral of the first coordinate times the function. Integrating this equality over the remaining coordinates gives the claimed formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_derivative_standardGaussian`.
