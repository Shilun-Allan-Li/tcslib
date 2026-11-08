<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Taylor.lean :: BooleanAnalysis.GaussianSpace.abs_sub_taylor_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Taylor Remainder Bound

**Claim.** For every natural number $m$, if $\\psi$ is $(m+1)$ times continuously differentiable and its $(m+1)$st derivative is bounded in absolute value by $C$, then the error after the degree-$m$ Taylor polynomial at $a$, evaluated at $a+b$, is at most $\frac{C}{(m+1)!}|b|^{m+1}$.

**Proof.** 1. Fix $a,b$ and reparameterize the line segment from $a$ to $a+b$ by $g(t)=\psi(a+bt)$. Repeated differentiation gives $g^{(j)}(t)=b^j\psi^{(j)}(a+bt)$ for every $j\le m+1$.

2. The Taylor polynomial of $g$ of degree $m$ at $0$, evaluated at $1$, is therefore the degree-$m$ Taylor polynomial of $\psi$ at $a$, evaluated with increment $b$.

3. Taylor's theorem with Lagrange remainder, applied to $g$ on $[0,1]$, gives some $t\in[0,1]$ for which the error equals $g^{(m+1)}(t)/(m+1)!$. Using the derivative formula, its absolute value is $|b|^{m+1}|\psi^{(m+1)}(a+bt)|/(m+1)!$. The assumed derivative bound now gives the result.
