<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedKKL.lean :: FABL.exercise9_30LogRemainder_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative logarithmic remainder

**Claim.** For $0\le\delta\le\tfrac12$, the expression $\log(1-\delta)-\log(1+\delta)+2\delta+\delta^3$ is nonnegative.

**Proof.** Let $R(x)=\log(1-x)-\log(1+x)+2x+x^3$. On $[0,1/2]$ both logarithm arguments are positive, so $R$ is continuous there and differentiable in its interior. Differentiating gives $R'(x)=-(1-x)^{-1}-(1+x)^{-1}+2+3x^2$, which simplifies to $x^2(1-3x^2)/((1-x)(1+x))$. The denominator is positive on the interval, and $x^2\le1/4$ implies $1-3x^2\ge1/4$; hence $R'(x)\ge0$ in the interior. The derivative criterion for monotonicity on a convex interval shows that $R$ is nondecreasing on the whole interval. Since $R(0)=0$, it follows that $R(\delta)\ge0$.
