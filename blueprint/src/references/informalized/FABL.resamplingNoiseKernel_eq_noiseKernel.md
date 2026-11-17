<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.resamplingNoiseKernel_eq_noiseKernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of noise kernels

**Claim.** For $0\le \rho\le1$, the resampling noise kernel equals the noise kernel with coordinate retention probability $(1+\rho)/2$.

**Proof.** Both kernels are independent products over coordinates. For each coordinate, the resampling construction first retains the original sign with probability $\rho$ and otherwise samples a uniform sign; the resulting coordinate law equals the law that keeps the sign with probability $(1+\rho)/2$ and flips it otherwise (`coordinateResamplingNoisePMF_eq_coordinateNoisePMF`). Applying this equality at every coordinate makes the product kernels equal.

**Key facts.** `FABL.coordinateResamplingNoisePMF_eq_coordinateNoisePMF`.
