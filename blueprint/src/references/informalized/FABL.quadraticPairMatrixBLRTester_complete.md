<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticPairMatrixBLRTester_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Matrix Tester

**Claim.** For every γ, the matrix tester accepts with probability 1 the matrix character defined by pairing with the rank-one self-matrix of γ.

**Proof.** The acceptance-probability identity for the matrix branch (quadraticPairMatrixBLRTester_acceptanceProbability) reduces the claim to completeness of the ordinary BLR tester on the function that sends a flattened matrix to its matrix-character value. A function on binary vectors is linear if it is a dot product with a fixed vector (isF₂Linear_iff_exists_dotProduct). Choose as that vector the flattening of the rank-one self-matrix of γ. The matrix-character flattening identity (binaryMatrixCharacter_unflattenBinaryMatrix) shows that the function evaluated on any flattened input is exactly this dot product. The BLR completeness theorem (blrFunctionTester_complete) therefore gives acceptance probability 1.

**Key facts.** `FABL.quadraticPairMatrixBLRTester_acceptanceProbability`, `FABL.isF₂Linear_iff_exists_dotProduct`, `FABL.binaryMatrixCharacter_unflattenBinaryMatrix`, `FABL.blrFunctionTester_complete`.
