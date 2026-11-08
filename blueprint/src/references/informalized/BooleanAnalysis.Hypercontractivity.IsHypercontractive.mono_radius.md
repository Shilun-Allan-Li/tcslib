<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.IsHypercontractive.mono_radius -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in the Radius

**Claim.** If $X$ is $(p,q,\rho)$-hypercontractive, has mean zero, and $0\leq\sigma\leq\rho$, then it is $(p,q,\sigma)$-hypercontractive.

**Proof.** If $\rho=0$, the bounds on $\sigma$ force $\sigma=0$, so the assertion is the original hypercontractivity statement. Otherwise $\rho>0$. Set $\theta=\sigma/\rho$; then $0\leq\theta\leq1$ and $\sigma=\theta\rho$. Fix $a,b$. The function with radius $\sigma$ is the convex combination
\[
a+\sigma bX=\theta(a+\rho bX)+(1-\theta)a.
\]
The triangle inequality for the $L^q$ norm bounds its norm by the weighted sum of the norms of these two terms. By the assumed contraction, the first norm is at most the $L^p$ norm of $a+bX$. For the constant term, mean zero and the fact that the measure is a probability measure give $\int(a+bX)\,d\mu=a$. Thus the norm of the constant $a$ is at most the $L^1$ norm of $a+bX$, which is at most its $L^p$ norm since $p\geq1$. The two weights sum to one, so the resulting bound is precisely the required $L^p$ bound. The exponent and radius conditions follow from the original assumptions and $0\leq\sigma\leq\rho<1$.
