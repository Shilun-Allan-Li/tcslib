<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.middleLayerIndicator_eq_one_iff_negative_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Coordinates on the Middle Layer

**Claim.** For every $m$ and every point $x$ in the sign cube of dimension $2m$, the middle-layer indicator equals $1$ exactly when exactly $m$ coordinates of $x$ equal $-1$.

**Proof.** First, each coordinate of the sign cube is either $1$ or $-1$, so the set of coordinates not equal to $1$ is exactly the set of coordinates equal to $-1$. The positive and negative coordinate sets therefore partition the $2m$ coordinates. Their cardinalities sum to $2m$. By definition, the indicator is $1$ precisely when the positive-coordinate count is $m$. If that count is $m$, the partition identity forces the negative-coordinate count to be $2m-m=m$. Conversely, if the negative-coordinate count is $m$, the same identity forces the positive-coordinate count to be $m$, so the indicator equals $1$.
