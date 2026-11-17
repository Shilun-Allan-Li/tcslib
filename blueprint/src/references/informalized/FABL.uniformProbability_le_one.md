<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.uniformProbability_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Probability Is at Most One

**Claim.** For a finite nonempty set $\Omega$ and a predicate $P$ on it, the uniform probability that $P$ holds is at most $1$.

**Proof.** At each $x\in\Omega$, the indicator of $P$ is either $0$ or $1$, hence is at most the constant $1$. Averaging preserves this inequality, and the uniform expectation of the constant $1$ is $1$. Therefore the probability is at most $1$.
