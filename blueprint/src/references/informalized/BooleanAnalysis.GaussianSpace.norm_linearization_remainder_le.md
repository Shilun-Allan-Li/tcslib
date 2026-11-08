<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/DiscreteApproximation.lean :: BooleanAnalysis.GaussianSpace.norm_linearization_remainder_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic linearization remainder

**Claim.** If $f$ is differentiable everywhere and its derivative is Lipschitz with constant $C$, then $\|f(y)-f(x)-D(x)(y-x)\|\leq C\|y-x\|^2$.

**Proof.** Fix $x$ and subtract the linear functional $D(x)$ from $f$, defining $g(z)=f(z)-D(x)(z)$. Its derivative at $z$ is $D(z)-D(x)$. On the closed ball centered at $x$ with radius $\|y-x\|$, the Lipschitz condition gives $\|D(z)-D(x)\|\leq C\|z-x\|\leq C\|y-x\|$. Both $x$ and $y$ lie in this ball. The mean-value estimate for a differentiable scalar-valued function on a convex set, with derivative norm bounded by $C\|y-x\|$, therefore gives $|g(y)-g(x)|\leq C\|y-x\|^2$. Expanding $g(y)-g(x)$ and using linearity of $D(x)$ identifies it with $f(y)-f(x)-D(x)(y-x)$; for a real-valued quantity its norm is its absolute value, yielding the result.
