<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.continuousOn_gaussianIsoperimetricInterior -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Gaussian Isoperimetric Interior Profile

**Claim.** The function assigning to each $\alpha\in(0,1)$ the standard Gaussian density at the standard Gaussian upper quantile of $\alpha$ is continuous on $(0,1)$.

**Proof.** On $(0,1)$, the extended real-valued quantile is continuous (continuousOn_standardGaussianUpperQuantileReal). The standard Gaussian density is continuous as a function of its real argument (continuous_standardGaussianDensity). Their composition is therefore continuous on $(0,1)$, and this composition is the Gaussian isoperimetric interior profile.

**Key facts.** `FABL.continuousOn_standardGaussianUpperQuantileReal`, `FABL.continuous_standardGaussianDensity`.
