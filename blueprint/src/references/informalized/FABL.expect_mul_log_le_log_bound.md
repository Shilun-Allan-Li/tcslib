<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SharpLevelOneInequality.lean :: FABL.expect_mul_log_le_log_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entropy Bound from a Pointwise Maximum

**Claim.** If a nonnegative function on a finite nonempty set has uniform mean $1$ and is bounded above by $M$, then the uniform expectation of $q(x)\log q(x)$ is at most $\log M$.

**Proof.** For each $x$, if $q(x)=0$, then $q(x)\log q(x)=0=q(x)\log M$. If $q(x)>0$, monotonicity of the logarithm and $q(x)\le M$ give $\log q(x)\le\log M$; multiplying by the nonnegative number $q(x)$ yields the same pointwise inequality. Averaging preserves the inequality. Since $\log M$ is constant, the resulting upper bound is $(\mathbb E_x q(x))\log M=\log M$, using the mean-one hypothesis.
