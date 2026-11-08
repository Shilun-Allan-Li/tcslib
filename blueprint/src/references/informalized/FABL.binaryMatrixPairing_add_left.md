<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.binaryMatrixPairing_add_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity in the First Matrix Argument

**Claim.** Pairing $A+B$ with the rank-one self-matrix formed from $z$ equals the sum of the pairings of $A$ and $B$ with that matrix.

**Proof.** Write the pairing as a double sum. At each index pair, distributivity gives $(A_{ij}+B_{ij})z_i z_j=A_{ij}z_i z_j+B_{ij}z_i z_j$. Distributing the finite sums over addition separates these terms into the two claimed pairings.
