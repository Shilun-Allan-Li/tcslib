<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.gowers_norm_mul_degree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance under a low-degree factor

**Claim.** If $g$ has degree at most $d$, multiplying $f$ pointwise by $g$ leaves the order-$(d+1)$ power-form Gowers norm unchanged.

**Proof.** Expand both power-form norms as averages over base points and direction tuples. For each fixed tuple, the order-$(d+1)$ Gowers product of the pointwise product $f\cdot g$ equals the product of the corresponding Gowers products of $f$ and $g$ (`gowers_product_mul_degree_le`). The degree hypothesis says that the latter product for $g$ is $1$, at every base point and tuple. Thus the two summands agree pointwise, so their finite sums and normalized averages agree.

**Key facts.** `LowDegreeTest.gowers_product_mul_degree_le`.
