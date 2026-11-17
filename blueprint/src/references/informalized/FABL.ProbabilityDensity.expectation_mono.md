<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/Viola.lean :: FABL.ProbabilityDensity.expectation_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of density expectation

**Claim.** If $F(x)\le G(x)$ for every $x$, then the expectation of $F$ under a probability density $\varphi$ is at most the expectation of $G$ under $\varphi$.

**Proof.** At each point $x$, multiplying $F(x)\le G(x)$ by the nonnegative number $\varphi(x)$ preserves the inequality, since $\varphi(x)\ge0$ (`ProbabilityDensity.nonneg`). Thus $\varphi(x)F(x)\le\varphi(x)G(x)$ pointwise. Summing these inequalities and dividing by the positive size of the cube preserves the order, so the uniform expectation of $\varphi F$ is at most that of $\varphi G$. These are precisely the two density expectations.

**Key facts.** `FABL.ProbabilityDensity.nonneg`.
