<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_congr_ae -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Almost Everywhere Invariance

**Claim.** If $f$ and $g$ agree almost everywhere under product standard Gaussian measure and $\rho\in[-1,1]$, then their Gaussian noise images at parameter $\rho$ also agree almost everywhere.

**Proof.** The endpoint map $(x,y)\mapsto \rho x+\sqrt{1-\rho^2}\,y$ preserves standard Gaussian measure ($\texttt{measurePreserving_gaussianEndpoint}$). Consequently, the almost everywhere equality of $f$ and $g$ pulls back to an almost everywhere equality after applying this map to a pair of independent Gaussian vectors. Fubini's theorem implies that for almost every fixed $x$, the two noise integrands agree for almost every $y$. Their integrals in $y$ are therefore equal, which gives the claimed almost everywhere equality of noise images.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianEndpoint`.
