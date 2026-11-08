<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.binaryMatrixPairing_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing with a Single-Entry Matrix

**Claim.** Pairing the matrix with a single entry equal to $1$ at $(i,j)$ against the rank-one self-matrix formed from $z$ gives $z_i z_j$.

**Proof.** In the double sum defining the pairing, the single-entry matrix contributes zero at every position except $(i,j)$. Thus the outer sum over the first index vanishes except at $i$, and within that term the inner sum vanishes except at $j$. The surviving summand is $1\cdot(z_i z_j)=z_i z_j$.
