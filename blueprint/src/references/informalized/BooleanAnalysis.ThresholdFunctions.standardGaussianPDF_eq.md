<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Explicit Gaussian Density

**Claim.** The standard Gaussian density is $\varphi(x)=\dfrac{1}{\sqrt{2\pi}}e^{-x^2/2}$ for every real $x$.

**Proof.** Unfold the standard Gaussian density as the real Gaussian density with mean $0$ and variance $1$. The defining Gaussian density formula reduces at those parameters to $(\sqrt{2\pi})^{-1}e^{-x^2/2}$, which proves the pointwise identity and hence equality of the functions.
