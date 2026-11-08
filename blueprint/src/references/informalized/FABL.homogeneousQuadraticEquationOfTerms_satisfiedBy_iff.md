<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.homogeneousQuadraticEquationOfTerms_satisfiedBy_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Equation from Listed Terms

**Claim.** The equation formed from a list of coordinate pairs is satisfied by $z$ if and only if the sum, with repetitions, of the products $z_a z_b$ over those pairs equals the right-hand side.

**Proof.** By definition, satisfaction means that the coefficient matrix paired with the rank-one matrix of $z$ equals the right-hand side. The coefficient matrix is the sum of the single-entry matrices indexed by the listed pairs. The pairing identity `binaryMatrixPairing_sum_single` evaluates this matrix pairing as the sum, over the list, of $z_a z_b$. Therefore the satisfaction condition is equivalent to the asserted equality, including repetitions in the list.

**Key facts.** `FABL.binaryMatrixPairing_sum_single`.
