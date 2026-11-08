<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Perturbation.lean :: BooleanAnalysis.GaussianSpace.Invariance.lipschitz_integral_sub_le_two_norm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz Stability of Integrals in $L^2$

**Claim.** For $U,V\in L^2(\mu)$ on a probability space and $c$-Lipschitz $\psi$, the difference of the expectations of $\psi(U)$ and $\psi(V)$ is at most $c$ times the $L^2$ norm of $U-V$.

**Proof.** The $L^2$ assumptions imply that $U,V$ are integrable, and composing an integrable function with a Lipschitz function preserves integrability (\texttt{integrable_lipschitz_comp}). Thus the difference of the two integrals is the integral of their pointwise difference. Its absolute value is bounded by the integral of $|\psi(U)-\psi(V)|$, which is at most $c\int|U-V|$ by the Lipschitz property. Finally, on a probability space the $L^1$ norm is at most the $L^2$ norm, so $\int|U-V|\le N_2(U-V)$. Multiplication by the nonnegative constant $c$ yields the claimed inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.integrable_lipschitz_comp`.
