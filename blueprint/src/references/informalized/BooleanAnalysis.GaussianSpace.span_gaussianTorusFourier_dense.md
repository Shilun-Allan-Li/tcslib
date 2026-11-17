<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Torus.lean :: BooleanAnalysis.GaussianSpace.span_gaussianTorusFourier_dense -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Density of Gaussian Torus Fourier Pullbacks

**Claim.** For a finite measure on $\mathbb R^n$ and finite $p\ge1$, the complex linear span of the pullbacks of torus Fourier characters under the specified Gaussian torus map is dense in $L^p$.

**Proof.** Consider the pullback map from the $L^p$ space on the image measure of the Gaussian torus map to $L^p(\mu)$. This map has dense range because it is surjective (surjective_gaussianTorus_pullback). On the torus, the complex span of the Fourier characters is dense in $L^p$ (span_mFourier_toLp_dense). A continuous linear map with dense range carries a dense subspace to a subspace whose closure is the whole target. Applying this to the pullback map identifies the image of those torus characters with the stated Gaussian torus Fourier functions, proving the density assertion.

**Key facts.** `BooleanAnalysis.GaussianSpace.surjective_gaussianTorus_pullback`, `BooleanAnalysis.GaussianSpace.span_mFourier_toLp_dense`.
