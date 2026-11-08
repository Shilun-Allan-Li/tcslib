<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticPolar_single_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polar Form on a Single-Coordinate Vector

**Claim.** The polar form of $x$ and the vector supported only at coordinate $i$ with value $c$ is $c$ times the sum of the coordinates $x_j$ for $j\ne i$.

**Proof.** Use the polar-form dot-product identity (`completeQuadraticPolar_eq_dotProduct`). For the single-coordinate vector, its polar frequency at coordinate $j$ is zero when $j=i$, and is $c$ otherwise: the sum over coordinates different from $j$ contains the one nonzero term exactly when $i\ne j$. The dot product is consequently the sum of $x_jc$ over $j\ne i$. Factoring out $c$ gives the claimed expression.

**Key facts.** `FABL.completeQuadraticPolar_eq_dotProduct`.
