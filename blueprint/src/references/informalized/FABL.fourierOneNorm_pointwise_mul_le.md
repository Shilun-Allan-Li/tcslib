<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/FourierNorms.lean :: FABL.fourierOneNorm_pointwise_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm of a product

**Claim.** For any two real-valued functions on the sign cube, the Fourier one-norm of their pointwise product is at most the product of their Fourier one-norms.

**Proof.** The coefficient of the pointwise product at $S$ is the sum over $T$ of the products of the coefficients of $f$ at $T\triangle S$ and of $g$ at $T$ (`fourierCoeff_pointwise_mul`). By the triangle inequality, the absolute value of this sum is at most the sum of the absolute values of its terms. Sum this bound over $S$ and exchange the finite sums. For each fixed $T$, the map $S\mapsto T\triangle S$ is a bijection of the subsets of coordinates, with itself as inverse. Therefore the sum over $S$ of $|\widehat f(T\triangle S)|$ equals the Fourier one-norm of $f$. Multiplying by $|\widehat g(T)|$ and summing over $T$ yields the product of the two Fourier one-norms.

**Key facts.** `FABL.fourierCoeff_pointwise_mul`.
