<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean :: BooleanAnalysis.Hypercontractivity.noiseKernel_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Nonnegativity of the noise kernel on the cube

**Claim.** Fix a natural number $n$ and a correlation parameter $\rho$ with $0\le\rho\le1$. Writing $\sigma(0)=1$ and $\sigma(1)=-1$, the noise kernel
\[
K_\rho(x,y)=\prod_{i=1}^{n}\frac{1+\rho\,\sigma(x_i)\,\sigma(y_i)}{2}
\]
is nonnegative for every pair of points $x,y\in\{0,1\}^n$.

**Proof.** The kernel is a finite product over the coordinates $i\in\{1,\dots,n\}$, so by the fact that a product of nonnegative reals is nonnegative (`Finset.prod_nonneg`) it suffices to show that each individual factor
\[
\frac{1+\rho\,\sigma(x_i)\,\sigma(y_i)}{2}
\]
is nonnegative.

Fix a coordinate $i$. Each of $x_i$ and $y_i$ is a single bit, so there are four cases, and in every one the product of signs $\sigma(x_i)\,\sigma(y_i)$ equals $\pm1$: it is $+1$ when the two bits agree (both $0$ or both $1$) and $-1$ when they differ. Thus the factor is either $(1+\rho)/2$ or $(1-\rho)/2$. In the first case $1+\rho\ge 1>0$ because $\rho\ge0$; in the second case $1-\rho\ge0$ because $\rho\le1$. Either way the factor is nonnegative, which is exactly what the per-factor goal required (the four cases are discharged by routine arithmetic from the two bounds $0\le\rho$ and $\rho\le1$).

**Key facts.** `Finset.prod_nonneg`.
