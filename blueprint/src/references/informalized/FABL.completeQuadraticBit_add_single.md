<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticBit_add_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single-coordinate addition law

**Claim.** Adding $c$ to coordinate $i$ changes the complete quadratic bit by $c\sum_{j\ne i}x_j$.

**Proof.** Apply the addition law for the complete quadratic bit with the added vector supported only at coordinate $i$. The quadratic bit of this single-coordinate vector is zero, while its polar term with $x$ is $c$ times the sum of the coordinates of $x$ other than $i$. Combining these gives the claimed change.

**Key facts.** `FABL.completeQuadraticBit_add`, `FABL.completeQuadraticBit_single`, `FABL.completeQuadraticPolar_single_right`.
