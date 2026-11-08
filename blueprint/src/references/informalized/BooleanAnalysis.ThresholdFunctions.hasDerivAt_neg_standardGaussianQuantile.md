<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.hasDerivAt_neg_standardGaussianQuantile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Negative Gaussian Quantile

**Claim.** For $a\in(0,1)$, the function $p\mapsto -Q(p)$ is differentiable at $a$ with derivative $-1/I(a)$.

**Proof.** The Gaussian quantile has derivative $Q'(a)=1/I(a)$ for $a\in(0,1)$ (\texttt{hasDerivAt_standardGaussianQuantile}). Negating the function negates its derivative, so the derivative of $-Q$ at $a$ is $-1/I(a)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianQuantile`.
