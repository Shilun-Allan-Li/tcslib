<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evenness of the Gaussian Density

**Claim.** For every real number $x$, the standard Gaussian density satisfies $\varphi(-x)=\varphi(x)$.

**Proof.** Use the explicit density formula `standardGaussianPDF_eq`. In that formula, replacing $x$ by $-x$ leaves the exponential unchanged because $(-x)^2=x^2$; the constant factor is unchanged as well. Thus the two density values agree.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq`.
