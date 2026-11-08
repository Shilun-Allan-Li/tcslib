<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.correlatedPairPMF_one_map_signPairCubeOneEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-coordinate correlated pair law

**Claim.** Transporting the law of a correlated pair of one-coordinate cube points to pairs of signs gives the law obtained by choosing a uniform first sign and applying the specified coordinate noise.

**Proof.** Compare the two probability laws at an arbitrary pair of signs $(x,y)$. Because the coordinate identification is an equivalence, the only cube pair mapped to $(x,y)$ is its inverse image, so the mapped probability is the probability of that cube pair. The point-probability formulas express this as the uniform probability of the first cube point times the conditional noise probability of the second (`correlatedPairPMF_apply`). In dimension one, the natural identification turns these factors into the uniform probability of $x$ and the single-coordinate noise probability of $y$ given $x$. Their product is exactly the point probability under the correlated sign law (`correlatedSignPairPMF_apply`). Thus the two laws agree at every pair.

**Key facts.** `FABL.correlatedPairPMF_apply`, `FABL.correlatedSignPairPMF_apply`.
