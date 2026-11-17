<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of probability expectation

**Claim.** If $f(x)\le g(x)$ at every outcome, then the expectation of $f$ under $p$ is at most the expectation of $g$.

**Proof.** By the finite-sum definition, the difference is controlled term by term: each weight $(p(x)).\mathrm{toReal}$ is nonnegative, so multiplying $f(x)\le g(x)$ by that weight preserves the inequality. Summing these inequalities over all outcomes gives the claimed comparison of expectations.
