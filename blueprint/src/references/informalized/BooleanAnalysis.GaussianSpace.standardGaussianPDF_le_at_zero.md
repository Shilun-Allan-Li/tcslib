<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.standardGaussianPDF_le_at_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum of the Standard Gaussian Density

**Claim.** For every real $x$, the standard Gaussian density satisfies $\varphi(x)\le\varphi(0)$.

**Proof.** Write $\varphi(x)=(\sqrt{2\pi})^{-1}e^{-x^2/2}$ using the density formula (`BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq`). Since $x^2\ge0$, the exponent $-x^2/2$ is nonpositive, and hence $e^{-x^2/2}\le1$. The constant $(\sqrt{2\pi})^{-1}$ is nonnegative, so multiplying preserves the inequality. At zero the exponential factor is $1$, giving the claimed bound.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq`.
