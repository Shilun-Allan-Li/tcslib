<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean :: toEuclideanLin_apply_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinates of a Matrix-Vector Product

**Claim.** For a real matrix $A$ and a vector $x$, the $i$-th coordinate of the linear image induced by $A$ is $\sum_j A_{ij}x_j$.

**Proof.** By the definition of the linear map induced by a matrix on Euclidean coordinate spaces, its value at $x$ has $i$-th coordinate given by the $i$-th row of $A$ paired with $x$. This is precisely $\sum_j A_{ij}x_j$.
