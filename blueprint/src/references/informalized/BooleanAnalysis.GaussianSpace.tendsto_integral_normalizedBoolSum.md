<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/NormalizedSums.lean :: BooleanAnalysis.GaussianSpace.tendsto_integral_normalizedBoolSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convergence of normalized Boolean sums

**Claim.** For each Lipschitz function $\psi:\mathbb R\to\mathbb R$, its expectation on the normalized sum of $m+1$ independent uniform signs converges to its standard Gaussian integral.

**Proof.** A quantitative comparison theorem (normalizedBoolSum_lipschitz_comparison) supplies a constant $K>0$ such that, for any positive number of signs, the absolute difference between the Boolean-sum expectation and the Gaussian integral is at most $Kc$ times the number of signs to the power $-1/4$, where $c$ is the Lipschitz constant. With $m+1$ signs this bound tends to zero, since $(m+1)^{-1}\to0$ and its positive one-quarter power also tends to zero. The expectation difference is therefore squeezed between zero and a quantity tending to zero, which proves the asserted convergence.

**Key facts.** `BooleanAnalysis.GaussianSpace.normalizedBoolSum_lipschitz_comparison`.

**Caveat.** The formal statement proves convergence of Lipschitz test-function integrals; the payload's separate de Moivre–Laplace description is not the declaration being proved.
