<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianMillsRatio.lean :: FABL.hasDerivAt_standardGaussianDensity_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Density Quotient Derivative

**Claim.** For every nonzero real $x$, the function $y\mapsto\phi(y)/y$ is differentiable at $x$ with derivative $-\phi(x)-\phi(x)/x^2$.

**Proof.** Apply the quotient rule to $\phi(y)/y$, using the Gaussian density derivative (`FABL.hasDerivAt_standardGaussianDensity_mills`) and the derivative $1$ of the identity function. At $y=x$, the quotient-rule expression is $((-x\phi(x))x-\phi(x))/x^2$. Since $x\ne0$, simplify this to $-\phi(x)-\phi(x)/x^2$, as claimed.

**Key facts.** `FABL.hasDerivAt_standardGaussianDensity_mills`.
