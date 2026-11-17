<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersNorm_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Gowers norm

**Claim.** For positive $k$, the Gowers norm of order $k$ is at most the Gowers norm of order $k+1$.

**Proof.** Apply the Gowers Cauchy–Schwarz inequality (`gowers_cauchy_schwarz`) to the family that extends the order-$k$ cube configuration to order $k+1$. Its inner product reduces to the order-$k$ diagonal inner product (`gowersInner_monotonicityFamily`), while the product of the norms over the enlarged cube is the order-$(k+1)$ norm raised to $2^k$ (`prod_gowersNorm_monotonicityFamily`). Thus the order-$k$ diagonal inner product is at most that power. By the power identity (`gowersNorm_pow`), it is the $2^k$-th power of the order-$k$ norm. Both norms are nonnegative (`gowersNorm_nonneg`), so taking the order-preserving $2^k$-th root proves the result.

**Key facts.** `FABL.gowers_cauchy_schwarz`, `FABL.gowersInner_monotonicityFamily`, `FABL.prod_gowersNorm_monotonicityFamily`, `FABL.gowersNorm_nonneg`, `FABL.gowersNorm_pow`.
