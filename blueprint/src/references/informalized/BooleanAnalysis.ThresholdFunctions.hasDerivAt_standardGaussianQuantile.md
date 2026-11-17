<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianQuantile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Gaussian Quantile

**Claim.** For $a\in(0,1)$, the Gaussian quantile $Q$ is differentiable at $a$ with derivative $1/I(a)$.

**Proof.** Use the local inverse differentiation theorem: if a function $f$ is differentiable at $Q(a)$ with nonzero derivative, and $Q$ is continuous at $a$ and satisfies $f(Q(y))=y$ for nearby $y$, then $Q'(a)=1/f'(Q(a))$. Here $f=\Phi$: the quantile is continuous at $a$ (\texttt{continuousAt_standardGaussianQuantile}), and $\Phi(Q(y))=y$ for every $y\in(0,1)$ (\texttt{standardGaussianCDF_quantile}). Also $\Phi'(Q(a))=\varphi(Q(a))=I(a)$ (\texttt{hasDerivAt_standardGaussianCDF} and the definition of $I$), and this is positive (\texttt{standardGaussianPDF_pos}). The theorem therefore gives $Q'(a)=1/I(a)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.continuousAt_standardGaussianQuantile`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_quantile`.
