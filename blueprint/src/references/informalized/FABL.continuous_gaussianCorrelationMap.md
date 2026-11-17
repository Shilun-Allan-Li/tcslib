<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.continuous_gaussianCorrelationMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Gaussian correlation map

**Claim.** For each real number $\rho$, the map $(u,v)\mapsto (u,\rho u+\sqrt{1-\rho^2}\,v)$ from the real plane to the plane with the $2$-norm is continuous.

**Proof.** For fixed $\rho$, the coefficient $\sqrt{1-\rho^2}$ is a real constant. The first output coordinate is a coordinate projection, and the second is a sum of scalar multiples of the input coordinates. Coordinate projections, scalar multiplication by a fixed real number, and addition are continuous. Therefore the pair-valued map is continuous; viewing its output in the $2$-norm plane preserves continuity.
