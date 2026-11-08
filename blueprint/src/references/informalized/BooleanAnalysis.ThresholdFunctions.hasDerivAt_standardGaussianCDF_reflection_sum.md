<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF_reflection_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Reflected Gaussian Distribution Sum

**Claim.** For every $x\in\mathbb R$, the function $t\mapsto\Phi(-t)+\Phi(t)$ is differentiable at $x$ with derivative $0$.

**Proof.** By the chain rule, the derivative of $\Phi(-t)$ at $t=x$ is $-\varphi(-x)$, while the derivative of $\Phi(t)$ is $\varphi(x)$ (\texttt{hasDerivAt_standardGaussianCDF}). The Gaussian density is even, so $\varphi(-x)=\varphi(x)$ (\texttt{standardGaussianPDF_neg}); hence the two derivatives sum to zero.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_neg`.
