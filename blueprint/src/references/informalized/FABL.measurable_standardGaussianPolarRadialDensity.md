<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.measurable_standardGaussianPolarRadialDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of the Radial Density

**Claim.** The function $r\mapsto\max(r,0)\,\varphi(r)\varphi(0)$ on $\mathbb{R}$ is measurable, where $\varphi$ is the standard Gaussian density.

**Proof.** The map $r\mapsto\max(r,0)$ and the Gaussian density $r\mapsto\varphi(r)$ are continuous, and $\varphi(0)$ is constant. Their product is therefore continuous, hence measurable.
