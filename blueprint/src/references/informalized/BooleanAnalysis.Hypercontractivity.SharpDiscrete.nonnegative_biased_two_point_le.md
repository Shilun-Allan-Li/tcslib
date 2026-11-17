<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointCalculus.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.nonnegative_biased_two_point_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Two-Point Inequality

**Claim.** For the stated normalized positive pair $\alpha<\beta$, the weighted quadratic expression with coefficient $r$ is bounded above by the weighted $p$-moment raised to $2/p$ for all nonnegative $u,v$.

**Proof.** If $\alpha u+\beta v=0$, nonnegativity and positivity of $\alpha,\beta$ force $u=v=0$, and the inequality is immediate. Otherwise, put $S=\alpha u+\beta v>0$, $k=S/2>0$, and $y=(\alpha u-\beta v)/S$. Nonnegativity of $u,v$ implies $-1\le y\le1$. Solving these definitions gives $u=k(1+y)/\alpha$ and $v=k(1-y)/\beta$.

The normalized biased quadratic inequality (\texttt{normalized\_biased\_quadratic\_le}) applies to this $y$. Its left side, after substituting the expressions for $u$ and $v$, is the desired quadratic expression divided by $k^2$. The weighted moment similarly factors as $k^p((1+y)^p+(1-y)^p)$, so its $2/p$ power is $k^2$ times the normalized right side. Since $k^2>0$, multiplying the normalized inequality by $k^2$ gives the result.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.normalized_biased_quadratic_le`.
