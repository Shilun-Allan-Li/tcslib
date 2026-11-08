<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityDelta_sq_log_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Bound

**Claim.** If the optimality parameter $\Delta$ is less than $1$, then $\Delta^2\log(1/\Delta)\leq 9\alpha^2\log(1/\alpha)$.

**Proof.** Write $\alpha$ for the Gaussian mass. Positivity of $\Delta$ and $\alpha$, together with $\alpha<\Delta$, shows that $1/\Delta\leq 1/\alpha$. Since the logarithm is increasing on positive reals, $\log(1/\Delta)\leq\log(1/\alpha)$. The assumption $\Delta<1$ also gives $\log(1/\Delta)\geq0$. The upper bound $\Delta\leq3\alpha$ gives $\Delta^2\leq9\alpha^2$. Multiplying this last inequality by the nonnegative logarithm first, then using the logarithm comparison with the nonnegative factor $9\alpha^2$, yields the desired bound after rearranging the product.

**Key facts.** `FABL.fknOptimalityDelta_pos`, `FABL.fknOptimalityGaussianMass_lt_delta`, `FABL.fknOptimalityDelta_lt_three_mul_gaussianMass`.
