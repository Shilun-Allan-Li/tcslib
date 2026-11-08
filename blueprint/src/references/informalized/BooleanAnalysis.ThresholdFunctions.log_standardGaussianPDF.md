<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.log_standardGaussianPDF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithm of the Gaussian density

**Claim.** For every real $x$, the logarithm of the standard Gaussian density is $-\log\sqrt{2\pi}-x^2/2$.

**Proof.** The standard Gaussian density has the expression $\varphi(x)=(\sqrt{2\pi})^{-1}e^{-x^2/2}$ (`standardGaussianPDF_eq`). Since $\sqrt{2\pi}\ne0$, apply the logarithm product and reciprocal identities, together with $\log(e^u)=u$. This gives $\log\varphi(x)=-\log\sqrt{2\pi}-x^2/2$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq`.
