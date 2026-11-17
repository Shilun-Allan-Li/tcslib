<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_memLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian noise preserves $L^p$ integrability

**Claim.** For a correlation $\rho\in[-1,1]$, an exponent $p\ge1$, and $f\in L^p(\gamma)$, Gaussian noise applied to $f$ also belongs to $L^p(\gamma)$.

**Proof.** The affine Gaussian endpoint map sends the product Gaussian measure to the Gaussian measure (\texttt{measurePreserving\_gaussianEndpoint}). Composing $f$ with this map preserves its $L^p$ integrability, and integrating in the second coordinate shows that the resulting Gaussian-noise function is almost everywhere strongly measurable. Its extended $L^p$ norm is at most that of $f$ by Gaussian noise contraction (\texttt{gaussianNoise\_contract}). Since $f$ has finite $L^p$ norm, this bound makes the noise function's norm finite as well. Together, strong measurability and finiteness of the norm give the claimed membership.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianEndpoint`, `BooleanAnalysis.GaussianSpace.gaussianNoise_contract`.
