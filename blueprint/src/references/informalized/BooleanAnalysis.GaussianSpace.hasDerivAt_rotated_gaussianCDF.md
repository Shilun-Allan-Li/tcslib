<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_rotated_gaussianCDF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a rotated Gaussian distribution function

**Claim.** Let $\Phi$ and $\varphi$ be the standard Gaussian distribution function and density. For every $t,y\in\mathbb R$, the function $\theta\mapsto\Phi((t-y\sin\theta)/\cos\theta)-\Phi(t)$ is differentiable at $0$, with derivative $-\varphi(t)y$.

**Proof.** The inner function $g(\theta)=(t-y\sin\theta)/\cos\theta$ satisfies $g(0)=t$ and $g'(0)=-y$, by the derivatives of sine and cosine and the quotient rule. The standard Gaussian distribution function has derivative $\varphi$ at every real argument (\texttt{hasDerivAt\_standardGaussianCDF}). By the chain rule, the derivative of $\Phi(g(\theta))$ at zero is $\varphi(t)(-y)$. Subtracting the constant $\Phi(t)$ does not change the derivative.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF`.
