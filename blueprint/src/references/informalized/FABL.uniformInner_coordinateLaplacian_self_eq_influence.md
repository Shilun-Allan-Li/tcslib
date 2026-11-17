<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DiscreteDerivatives.lean :: FABL.uniformInner_coordinateLaplacian_self_eq_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Laplacian and coordinate influence

**Claim.** For a real-valued function on the Boolean cube, the uniform squared norm of its coordinate Laplacian equals its influence in that coordinate.

**Proof.** Express the uniform inner product as the uniform average of pointwise products. At each input $x$, the coordinate Laplacian equals the sign of coordinate $i$ times the discrete derivative in that coordinate (\texttt{FABL.coordinateLaplacian_eq_signValue_mul_discreteDerivative}). Every coordinate sign is either $1$ or $-1$, so its square is $1$. Consequently, the square of the Laplacian at $x$ equals the square of the discrete derivative there. Averaging over $x$ gives the definition of the influence.

**Key facts.** `FABL.coordinateLaplacian_eq_signValue_mul_discreteDerivative`.
