<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.correlatedSignProjection_eq_inner -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Projection as an Inner Product

**Claim.** For every vector $t$ in the real two-dimensional correlation plane and every pair of signs $(x,y)$, the projection $x t_1+y t_2$ equals the inner product of $t$ with the vector $(x,y)$, with the signs viewed as real numbers.

**Proof.** Unpack the projection and the correlated sign vector. The inner product on the real product plane is the sum of the products of corresponding coordinates, so it is exactly $\operatorname{signValue}(x)t_1+\operatorname{signValue}(y)t_2$, the defining expression for the projection.
