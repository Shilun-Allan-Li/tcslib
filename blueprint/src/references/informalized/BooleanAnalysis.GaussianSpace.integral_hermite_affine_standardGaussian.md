<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Noise.lean :: BooleanAnalysis.GaussianSpace.integral_hermite_affine_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite polynomial Gaussian averaging

**Claim.** For $\rho^2+s^2=1$, the standard Gaussian average of the degree $k$ Hermite polynomial at $\rho x+sy$ equals $\rho^k$ times that polynomial evaluated at $x$.

**Proof.** Use induction advancing two degrees at a time. In degree zero, the Hermite polynomial is constant, so the identity holds. In degree one, write the polynomial at $\rho x+sy$ as its constant-in-$y$ term plus a multiple of $y$; the standard Gaussian mean is zero, leaving $\rho x$, as claimed. For the step from degrees $k$ and $k+1$ to $k+2$, apply the affine integral recurrence (`integral_hermite_affine_recurrence`) and substitute the two induction hypotheses. The Hermite recurrence, together with its derivative formula (`derivative_hermite_succ`), identifies the resulting expression with $\rho^{k+2}H_{k+2}(x)$.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_hermite_affine_recurrence`, `BooleanAnalysis.GaussianSpace.derivative_hermite_succ`.
