<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.correlatedPairPMF_map_pairCoordinatesEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independent coordinate decomposition

**Claim.** After rearranging a correlated pair of sign vectors into its coordinate pairs, its law is the product of the single-coordinate correlated sign laws.

**Proof.** It suffices to compare the probability of each possible coordinate-pair sequence $z$. Since the coordinate rearrangement is an equivalence, the only original pair mapped to $z$ is its inverse image; thus the probability after mapping is the probability of that inverse image. Write it as $(x,y)$. The point-probability formula for the correlated pair gives the uniform probability of $x$ times the noise-kernel probability of $y$ given $x$ (`correlatedPairPMF_apply`). By the product definition of the noise kernel, the latter probability is the product, over coordinates $i$, of the probability that the coordinate noise sends $x_i$ to $y_i$. The uniform probability of a cube vector is $2^{-n}$, which is the product of $n$ uniform single-sign probabilities. Combining these factors coordinate by coordinate gives the product of the single-coordinate correlated-pair probabilities, by the point-probability formula for that law (`correlatedSignPairPMF_apply`). The product law therefore assigns the same probability to every $z$, proving equality of the distributions.

**Key facts.** `FABL.correlatedPairPMF_apply`, `FABL.independentProductPMF_apply`, `FABL.correlatedSignPairPMF_apply`.
