<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SharpLevelOneInequality.lean :: FABL.expect_mul_sub_log_expect_exp_le_entropy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entropy Variational Inequality

**Claim.** For nonnegative $q$ of uniform mean $1$ on a finite nonempty set and any real-valued function $y$, the uniform expectation of $q(x)y(x)$ minus the logarithm of the uniform expectation of $\exp(y(x))$ is at most the uniform expectation of $q(x)\log q(x)$.

**Proof.** Set $Z=\mathbb E_x\exp(y(x))$, which is positive because every term in this finite average is positive. The pointwise Gibbs inequality (\texttt{FABL.gibbs\_pointwise}) gives, for each $x$,
\[
q(x)y(x)-q(x)\log Z-q(x)\log q(x)\le \frac{\exp(y(x))}{Z}-q(x).
\]
Average both sides. On the left, linearity of expectation and $\mathbb E_x q(x)=1$ give $\mathbb E_x[q(x)y(x)]-\log Z-\mathbb E_x[q(x)\log q(x)]$. On the right, the average is $Z/Z-1=0$. Rearranging yields the asserted inequality.

**Key facts.** `FABL.gibbs_pointwise`.
