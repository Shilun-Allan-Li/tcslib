<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_compose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Gaussian Noise

**Claim.** For $\rho,\sigma\in[-1,1]$ and integrable $f$, applying Gaussian noise at parameter $\sigma$ and then at parameter $\rho$ agrees almost everywhere with applying it once at parameter $\rho\sigma$.

**Proof.** Replace $f$ by a strongly measurable representative equal to it almost everywhere. The noise operator preserves almost everywhere equality ($\texttt{gaussianNoise_congr_ae}$), so this replacement is valid both inside the iterated noise operation and in the final noise operation; integrability is likewise retained by almost everywhere modification. For the strongly measurable representative, the composition identity is supplied by $\texttt{gaussianNoise_compose_stronglyMeasurable}$. Finally, the product of two correlations in $[-1,1]$ is again in $[-1,1]$ ($\texttt{correlation_mul_mem}$), allowing the almost everywhere invariance result to identify the noise applied at $\rho\sigma$ to the original function with that applied to its representative. Chaining these almost everywhere equalities proves the assertion.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianNoise_congr_ae`, `BooleanAnalysis.GaussianSpace.gaussianNoise_compose_stronglyMeasurable`, `BooleanAnalysis.GaussianSpace.correlation_mul_mem`.
