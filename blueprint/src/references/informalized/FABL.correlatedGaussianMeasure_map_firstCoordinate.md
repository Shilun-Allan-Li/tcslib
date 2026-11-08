<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.correlatedGaussianMeasure_map_firstCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Gaussian marginal

**Claim.** For every $\rho\in\mathbb R$, the first coordinate of the correlated pair has the standard Gaussian law.

**Proof.** The correlated measure is the image of the product of two standard Gaussian measures under the map sending $(u,v)$ to $(u,\rho u+\sqrt{1-\rho^2}v)$. Projecting this image onto the first coordinate is the same as first composing the two maps. That composition is simply $(u,v)\mapsto u$. The first marginal of a product measure is its first factor, and the product measure here has standard Gaussian first factor. Hence the first coordinate has standard Gaussian law.

**Key facts.** `FABL.continuous_correlationFirstCoordinate`, `FABL.continuous_gaussianCorrelationMap`.
