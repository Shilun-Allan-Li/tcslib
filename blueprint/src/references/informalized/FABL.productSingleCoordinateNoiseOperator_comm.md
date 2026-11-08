<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productSingleCoordinateNoiseOperator_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Commutation of coordinate noise operators

**Claim.** For two coordinates and arbitrary real parameters, the corresponding single-coordinate noise operators commute on every function.

**Proof.** Apply the Fourier-coefficient map associated with the given orthonormal basis to both sides. This map is injective (`FiniteFourierBasis.fourierCoeff_injective`), so it suffices to check equality of every coefficient. At a multi-index $a$, applying the operator in coordinate $i$ multiplies the coefficient by $1$ when $a_i$ is the constant basis index and by $\rho$ otherwise; the corresponding multiplier for coordinate $j$ is $1$ or $\sigma$ according to whether $a_j$ is the constant index (`FiniteFourierBasis.fourierCoeff_productSingleCoordinateNoiseOperator`). In either order the coefficient is multiplied by the same two real factors, whose product is unchanged by commutativity of multiplication. Hence all coefficients agree, and injectivity gives equality of the functions.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_injective`, `FABL.FiniteFourierBasis.fourierCoeff_productSingleCoordinateNoiseOperator`.
