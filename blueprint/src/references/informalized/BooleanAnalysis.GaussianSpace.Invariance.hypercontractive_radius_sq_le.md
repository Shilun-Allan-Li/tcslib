<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdMoments.lean :: BooleanAnalysis.GaussianSpace.Invariance.hypercontractive_radius_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared hypercontractive radius bound

**Claim.** Under the stated assumptions, the squared hypercontractive radius satisfies $\rho^2\le 2/3$.

**Proof.** First, the affine third-moment estimate, applied with constant term $1$ and slope $b$, implies that whenever $b^2=\rho^2$, the integral of $|1+bX|^3$ is at most $3$: the quantity inside its right-hand power is $1+(b/\rho)^2=2$, and $2^{3/2}\le3$. Apply this once with $b=\rho$ and once with $b=-\rho$. Thus both integrals, for $|1+\rho X|^3$ and $|1-\rho X|^3$, are at most $3$.

The pointwise inequality $2+6t^2\le |1+t|^3+|1-t|^3$, applied to $t=\rho X$, can now be integrated. The required integrability follows from $X\in L^3$ and the fact that constants and scalar multiples preserve this membership. Since $\mu$ is a probability measure, the integral of the constant $2$ is $2$; the second-moment normalization makes the integral of $6(\rho X)^2$ equal to $6\rho^2$. The right side is at most $3+3=6$. Therefore $2+6\rho^2\le6$, which rearranges to $\rho^2\le2/3$.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.affine_abs_third_moment_le`, `BooleanAnalysis.GaussianSpace.Invariance.two_rpow_three_halves_le_three`, `BooleanAnalysis.GaussianSpace.Invariance.two_add_six_sq_le_abs_cubes`.
