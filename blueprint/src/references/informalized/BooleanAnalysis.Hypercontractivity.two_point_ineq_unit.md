<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean :: BooleanAnalysis.Hypercontractivity.two_point_ineq_unit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-sided two-point power inequality

**Claim.** For $1\le p\le2$ and $0\le b\le1$, $(1+(p-1)b^2)^{p/2}$ is at most the average of $(1+b)^p$ and $(1-b)^p$.

**Proof.** Define $F(b)=((1+b)^p+(1-b)^p)/2-(1+(p-1)b^2)^{p/2}$. The proof shows $F$ is nondecreasing on $(0,1)$ by proving its derivative is nonnegative there. Differentiating gives a term proportional to $(1+b)^{p-1}-(1-b)^{p-1}$ minus the derivative contribution from the second power. To control the difference, consider $G(x)=(1+x)^{p-1}-(1-x)^{p-1}-2(p-1)x$. Its derivative is $(p-1)((1+x)^{p-2}+(1-x)^{p-2}-2)$. The sum of powers is at least twice their geometric mean, and that geometric mean is $((1+x)(1-x))^{(p-2)/2}\ge1$, since $(1+x)(1-x)\le1$ and $(p-2)/2\le0$. Thus $G'\ge0$; the mean value theorem from $0$ to $b$ gives $G(b)\ge G(0)=0$. In the formula for $F'$, this lower bound, together with $(1+(p-1)b^2)^{p/2-1}\le1$, implies $F'(b)\ge0$. For any $b\in[0,1]$, the mean value theorem on $[0,b]$ then gives $F(b)\ge F(0)=0$ (and $b=0$ is immediate), which is exactly the claim.
