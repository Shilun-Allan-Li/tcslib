<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.variance_dualBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance under Boolean duality

**Claim.** If $f^*(x)=-f(-x)$ is the dual Boolean function, then $\operatorname{Var}(f^*)=\operatorname{Var}(f)$.

**Proof.** For each Boolean function, variance equals one minus the square of its mean, by `variance_eq_four_mul_probabilities`. The mean of the dual is the negative of the original mean, by `mean_dualBooleanFunction`. Applying these facts, the dual variance is $1-(-\mathbb E[f])^2=1-(\mathbb E[f])^2$, which is the variance of $f$.

**Key facts.** `FABL.variance_eq_four_mul_probabilities`, `FABL.mean_dualBooleanFunction`.
