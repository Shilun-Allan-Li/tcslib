<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductBounds.lean :: BooleanAnalysis.GaussianSpace.abs_productHessian_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Majorant for a Hessian Score

**Claim.** For $|a|\le1$, the absolute value of the Hessian score multiplied by $a$ is bounded by the stated quadratic expression.

**Proof.** Write $u=z_i-c_i$ and $w=z_j-c_j$. The inequality $|uw|\le (u^2+w^2)/2$ follows from $(|u|-|w|)^2\ge0$. The diagonal correction is either $1/v$ or zero, so its absolute value is at most $1/v$. Since $|a|\le1$, multiplying the score by $a$ cannot increase its absolute value. The triangle inequality then bounds the score by $|uw|/v^2+1/v$; using the quadratic estimate gives the claimed majorant.
