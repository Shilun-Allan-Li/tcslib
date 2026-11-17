<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/ProbabilityDensityPushforward.lean :: FABL.ProbabilityDensity.sq_expectation_le_expectation_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square of an expectation

**Claim.** For a probability density $\rho$ on the Boolean cube and a real-valued function $f$, the square of the expectation of $f$ under $\rho$ is at most the expectation of $f^2$ under $\rho$.

**Proof.** Apply the finite Cauchy–Schwarz inequality to the functions $x\mapsto\sqrt{\rho(x)}$ and $x\mapsto\sqrt{\rho(x)}f(x)$. Their expected product is the expectation of $f$ under $\rho$, since $\sqrt{\rho(x)}\sqrt{\rho(x)}=\rho(x)$ by nonnegativity. The expected square of the first function is $1$: its pointwise square is $\rho(x)$, whose expectation is $1$ by normalization. The expected square of the second function is the expectation of $f(x)^2$ under $\rho$, again using $(\sqrt{\rho(x)})^2=\rho(x)$. Substitution into Cauchy–Schwarz gives the desired inequality.

**Key facts.** `FABL.ProbabilityDensity.nonneg`, `FABL.ProbabilityDensity.expect_eq_one`.
