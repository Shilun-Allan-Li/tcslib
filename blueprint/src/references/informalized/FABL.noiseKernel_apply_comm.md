<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.noiseKernel_apply_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the Noise Kernel

**Claim.** Interchanging $x$ and $y$ leaves the noise kernel's value unchanged.

**Proof.** The independent product formula writes the kernel's value at $y$ given $x$ as the product, over coordinates, of the corresponding one-coordinate noise probabilities (`independentProductPMF_apply`). At each coordinate, that probability is symmetric in the input and output signs (`coordinateNoisePMF_apply_comm`). Therefore every factor, and hence the full product, is unchanged when $x$ and $y$ are interchanged.

**Key facts.** `FABL.independentProductPMF_apply`, `FABL.coordinateNoisePMF_apply_comm`.
