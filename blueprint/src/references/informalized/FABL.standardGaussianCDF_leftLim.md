<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianCDF_leftLim -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left Continuity of the Gaussian CDF

**Claim.** At every real $x$, the left-hand limit of the standard Gaussian cumulative distribution function equals its value at $x$.

**Proof.** The standard Gaussian has no atoms: the measure it assigns to the singleton $\{x\}$ is zero, as follows from its absolute continuity with respect to Lebesgue measure. The measure of this singleton also equals the jump of its cumulative distribution function at $x$. Hence that jump vanishes, so the left-hand limit is at least the value at $x$. Conversely, monotonicity of the cumulative distribution function bounds its left-hand limit above by its value at $x$. The two bounds give equality.
