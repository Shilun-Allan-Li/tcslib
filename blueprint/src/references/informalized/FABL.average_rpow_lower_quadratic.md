<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.average_rpow_lower_quadratic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Lower Bound for Averaged Powers

**Claim.** If $1\le p\le2$ and $|e|\le1$, then $1+\frac{p(p-1)}2e^2\le\frac{(1+e)^p+(1-e)^p}{2}$.

**Proof.** Define $F(z)=\frac{(1+z)^p+(1-z)^p}{2}-1-\frac{p(p-1)}2z^2$ on $[-1,1]$. The proof shows that $F$ is continuous there and twice differentiable in the interior, with
\[F''(z)=\frac{p(p-1)}2\big((1+z)^{p-2}+(1-z)^{p-2}-2\big).\]
For interior $z$, put $U=(1+z)^{p-2}$ and $V=(1-z)^{p-2}$. Since $(1+z)(1-z)=1-z^2\le1$ and $p-2\le0$, the product $UV=(1-z^2)^{p-2}$ is at least $1$. Thus $U+V\ge2\sqrt{UV}\ge2$. Also $p(p-1)/2\ge0$, so $F''(z)\ge0$ and $F$ is convex on the interval.
Now $e,-e\in[-1,1]$. Convexity at their midpoint gives $F(0)\le(F(e)+F(-e))/2$. The definition makes $F(0)=0$ and $F(-e)=F(e)$, so $F(e)\ge0$. Rearranging this inequality is the claimed bound.
