<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianPDF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Standard Gaussian Density

**Claim.** For every $x\in\mathbb R$, the standard Gaussian density is differentiable at $x$ with derivative $-x\varphi(x)$.

**Proof.** Write the density as $\varphi(y)=(2\pi)^{-1/2}\exp(-y^2/2)$ (\texttt{standardGaussianPDF_eq}). The exponent has derivative $-x$ at $x$, so the chain rule gives derivative $(2\pi)^{-1/2}e^{-x^2/2}(-x)$. The constant factor is precisely the one in $\varphi(x)$, giving $-x\varphi(x)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq`.
