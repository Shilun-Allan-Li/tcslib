<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.correlatedPairPMF_apply_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exchange symmetry of a correlated pair

**Claim.** The point probability assigned to $(x,y)$ by the correlated-pair law equals the point probability assigned to $(y,x)$.

**Proof.** Express each point probability as the uniform mass of its first coordinate times the noise-kernel probability of the second coordinate given the first (`correlatedPairPMF_apply`). The noise kernel is symmetric in its two arguments (`noiseKernel_apply_comm`), so the conditional factors in the two expressions agree. The uniform distribution on the finite cube assigns the same mass to every point, hence the initial-coordinate factors agree as well. Therefore the two joint point probabilities are equal.

**Key facts.** `FABL.correlatedPairPMF_apply`, `FABL.noiseKernel_apply_comm`.
