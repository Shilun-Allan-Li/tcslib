<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.standardGaussianPlaneDensity_polar -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian plane density in polar coordinates

**Claim.** For every $p=(r,\theta)\in\mathbb R\times\mathbb R$, multiplying the standard Gaussian plane density at the point with polar coordinates $(r,\theta)$ by $r$ gives the standard Gaussian polar radial density at $r$.

**Proof.** The point with polar coordinates $(r,\theta)$ is $(r\cos\theta,r\sin\theta)$. By the Gaussian product identity in polar coordinates, the product of the one-dimensional densities at these two coordinates equals the product of the densities at $r$ and at $0$ (`gaussianPDF_mul_polar`). Multiplying by the common factor $r$ gives exactly the stated radial density.

**Key facts.** `FABL.gaussianPDF_mul_polar`.
