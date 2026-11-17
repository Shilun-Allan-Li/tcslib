<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.correlatedSignProjection_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling the Sign Projection

**Claim.** For every real scalar $a$, vector $t$ in the real two-dimensional correlation plane, and pair of signs $(x,y)$, the projection at $at$ is $a$ times the projection at $t$.

**Proof.** The two coordinates of the scalar multiple $at$ are $a t_1$ and $a t_2$. Substituting them into the projection gives $x(a t_1)+y(a t_2)$. Distributivity factors out $a$, leaving $a(xt_1+yt_2)$, as required.
