<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SmoothVariation.lean :: BooleanAnalysis.GaussianSpace.lintegral_gaussianLinearMap_family -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian moment identity for a family

**Claim.** For a continuous family of linear functionals, the extended Gaussian integral of $|L(z_1)(z_2)|$ over two independent standard Gaussian vectors equals $2\varphi(0)$ times the extended Gaussian integral of the Euclidean norm of the coefficient vector of $L(x)$.

**Proof.** Integrate first in the second Gaussian vector, using the absolute-moment identity for a single linear functional (\texttt{BooleanAnalysis.GaussianSpace.lintegral_abs_gaussianLinearMap}). At each fixed first vector $x$, this gives the square root of the sum of squared coordinate values of $L(x)$, multiplied by $2\varphi(0)$. Tonelli’s theorem for nonnegative integrands permits this iterated integration over the product Gaussian measure. Pulling the constant factor outside the remaining integral yields the stated identity.

**Key facts.** `BooleanAnalysis.GaussianSpace.lintegral_abs_gaussianLinearMap`.
