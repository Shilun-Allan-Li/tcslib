<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.binaryMatrixPairing_sum_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing a Sum of Single-Entry Matrices

**Claim.** Pairing the sum of the single-entry matrices specified by a finite list of index pairs with the rank-one self-matrix formed from $z$ equals the sum of $z_i z_j$ over those pairs, including repetitions.

**Proof.** Proceed by induction on the list. For the empty list, both sums are zero. For a list beginning with a pair $(i,j)$ followed by a tail, the matrix sum splits into the single-entry matrix for $(i,j)$ plus the matrix sum for the tail. Additivity of the pairing in its first matrix argument ($\texttt{binaryMatrixPairing_add_left}$) splits the pairing accordingly. The single-entry pairing formula ($\texttt{binaryMatrixPairing_single}$) evaluates the first part as $z_i z_j$, and the induction hypothesis evaluates the tail part as its corresponding sum. Together these are precisely the sum over the whole list.

**Key facts.** `FABL.binaryMatrixPairing_add_left`, `FABL.binaryMatrixPairing_single`.
