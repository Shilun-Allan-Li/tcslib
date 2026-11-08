<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.gaussian_surface_normalization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian density normalization

**Claim.** The standard Gaussian density satisfies $\sqrt{\pi/2}\,2\varphi(0)=1$.

**Proof.** First rewrite $2\sqrt{\pi/2}$ as $\sqrt{2\pi}$, using positivity of the quantities under the square roots. The standard Gaussian density formula (`standardGaussianPDF_eq`) gives $\varphi(0)=(\sqrt{2\pi})^{-1}$, since the exponential factor at zero is one. Therefore the stated product is $\sqrt{2\pi}\,(\sqrt{2\pi})^{-1}=1$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq`.
