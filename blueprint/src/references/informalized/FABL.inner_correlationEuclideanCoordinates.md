<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.inner_correlationEuclideanCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner product under coordinate identification

**Claim.** For a vector in the two-dimensional real correlation plane and a Euclidean vector, applying the coordinate identifications on the respective sides preserves the inner product.

**Proof.** Write the correlation-plane vector as a pair $(z_0,z_1)$ and the Euclidean vector as $(t_0,t_1)$. Under the given coordinate identifications, both inner products expand to $z_0t_0+z_1t_1$: the Euclidean inner product is the sum over its two coordinates, and the pair-space inner product has the same coordinatewise formula. Hence they are equal.
