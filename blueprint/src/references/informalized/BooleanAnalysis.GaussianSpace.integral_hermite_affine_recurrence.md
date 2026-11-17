<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Noise.lean :: BooleanAnalysis.GaussianSpace.integral_hermite_affine_recurrence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite affine integral recurrence

**Claim.** For each $k$, the Gaussian integral of the Hermite polynomial of degree $k+2$ at $\rho x+sy$ equals $\rho x$ times the degree $k+1$ integral minus $(k+1)\rho^2$ times the degree $k$ integral.

**Proof.** The proof first establishes integrability of each affine Hermite polynomial and of its product with $y$, using polynomial times affine integrability (`integrable_polynomial_mul_affine_standardGaussian`). Gaussian integration by parts in the form $\int yP(a+by)\,d\gamma=b\int P'(a+by)\,d\gamma$ (`integral_id_mul_polynomial_affine_standardGaussian`), together with the derivative formula for Hermite polynomials (`derivative_hermite_succ`), gives $\int yH_{k+1}(\rho x+sy)\,d\gamma=s(k+1)\int H_k(\rho x+sy)\,d\gamma$. Pointwise, the Hermite recurrence expresses $H_{k+2}(u)$ as $uH_{k+1}(u)-H'_{k+1}(u)$, where $u=\rho x+sy$. Integrate this identity, splitting the affine factor into $\rho x$ and $sy$ contributions. Substitute the integration-by-parts identity for the latter. The resulting coefficient of the degree $k$ integral is $s^2(k+1)-(k+1)$, which equals $-(k+1)\rho^2$ because $\rho^2+s^2=1$. This is the required recurrence.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_polynomial_mul_affine_standardGaussian`, `BooleanAnalysis.GaussianSpace.integral_id_mul_polynomial_affine_standardGaussian`, `BooleanAnalysis.GaussianSpace.derivative_hermite_succ`.
