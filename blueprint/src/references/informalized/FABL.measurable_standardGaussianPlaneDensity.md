<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.measurable_standardGaussianPlaneDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of the Gaussian Plane Density

**Claim.** The function $(u,v)\mapsto\varphi(u)\varphi(v)$ on $\mathbb{R}^2$ is measurable, where $\varphi$ is the standard Gaussian density.

**Proof.** The standard Gaussian density is a continuous function of its real argument. The coordinate projections $(u,v)\mapsto u$ and $(u,v)\mapsto v$ are continuous, so composing the density with either projection gives a continuous function on $\mathbb{R}^2$. Their product is continuous, hence measurable.
