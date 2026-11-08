<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell.lean :: BooleanAnalysis.GaussianSpace.borell_balanced -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced Gaussian noise stability bound

**Claim.** For $0<\rho<1$, every measurable function $f$ taking values in $[-1,1]$ and having Gaussian mean zero has noise stability at most $1-2\arccos(\rho)/\pi$.

**Proof.** Define $g=(f+1)/2$, so $g$ takes values in $[0,1]$. The boundedness and measurability of $f$ give the square integrability needed for the affine noise stability identity. By linearity of integration and the zero mean of $f$, the Gaussian mean of $g$ is $1/2$. Borell's inequality bounds the noise stability of $g$ by that of a halfspace with Gaussian measure $1/2$ (Borell's theorem, `BooleanAnalysis.GaussianSpace.borell`). The halfspace stability at mean $1/2$ is the Gaussian quadrant probability (`BooleanAnalysis.GaussianSpace.gaussianHalfspaceStability_half`), which Sheppard's formula identifies as $1/2-\arccos(\rho)/(2\pi)$ (`BooleanAnalysis.ThresholdFunctions.sheppard_formula`). Finally, the affine noise stability identity expresses the stability of $g=(f+1)/2$ as one quarter the stability of $f$ plus the constant and mean terms (`BooleanAnalysis.GaussianSpace.gaussianNoiseStability_affine`). Since the mean of $f$ is zero, rearranging the bound yields the stated inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.borell`, `BooleanAnalysis.GaussianSpace.gaussianHalfspaceStability_half`, `BooleanAnalysis.ThresholdFunctions.sheppard_formula`, `BooleanAnalysis.GaussianSpace.gaussianNoiseStability_affine`.
