<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Kernel.lean :: BooleanAnalysis.GaussianSpace.eLpNorm_integral_prod_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Contraction of Integration in $L^p$

**Claim.** If $1\le p\le\infty$, $mu$ is s-finite, $nu$ is a probability measure, and $F$ is almost everywhere strongly measurable on the product, then integrating $F(x,y)$ over $y$ gives an $L^p(\mu)$ norm no greater than the $L^p(\mu\otimes\nu)$ norm of $F$.

**Proof.** For almost every $x$, the section $y\mapsto F(x,y)$ is almost everywhere strongly measurable. The norm of its integral is bounded by the integral of its absolute value, and since $\nu$ is a probability measure, this is its $L^1(\nu)$ norm. Monotonicity of norms as the exponent increases from $1$ to $p$ bounds this by the section's $L^p(\nu)$ norm. If $p=\infty$, this pointwise section bound and the almost-everywhere bound of sections by the product essential supremum imply the desired essential-supremum inequality. For finite $p$, raise the section inequality to the power $p$, integrate over $x$, and use Tonelli's theorem to identify the resulting iterated integral with the product-space integral. Taking the $p$th root gives the asserted norm inequality.
