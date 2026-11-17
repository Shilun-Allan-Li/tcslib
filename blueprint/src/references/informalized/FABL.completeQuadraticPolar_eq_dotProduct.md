<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.completeQuadraticPolar_eq_dotProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polar Form as a Dot Product

**Claim.** For $x,z\in\mathbb F_2^n$, the polar form equals the dot product of $x$ with the vector whose $i$th coordinate is the sum of the $z_j$ for $j\ne i$.

**Proof.** Expand the polar form into the sum of the terms $x_i z_j$ and the terms $z_i x_j$ over pairs $i<j$. In the first sum, collect terms by the coordinate multiplying $x_i$; its coefficient is the sum of $z_j$ over $j>i$. In the second, interchange the order of summation and collect terms by the coordinate multiplying $x_j$; its coefficient is the sum of $z_i$ over $i<j$. For each fixed coordinate, these two index sets partition all coordinates other than that coordinate. Their combined coefficient is therefore the sum of $z$ over its complement. Summing these coefficients times the corresponding coordinates of $x$ is precisely the stated dot product.
