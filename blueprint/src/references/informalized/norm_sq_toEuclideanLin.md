<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean :: norm_sq_toEuclideanLin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared norm of a linear image

**Claim.** For a real matrix $A$ defining a linear map from $\mathbb{R}^d$ to $\mathbb{R}^k$ and a vector $x$, the squared Euclidean norm of $Ax$ is the sum of the squares of its coordinates.

**Proof.** Apply the coordinate formula for the Euclidean norm to the vector $Ax$: its norm is the square root of the sum of the squared absolute values of its coordinates. Squaring removes the square root, and $|(Ax)_i|^2=(Ax)_i^2$ for every coordinate. This yields the asserted sum.
