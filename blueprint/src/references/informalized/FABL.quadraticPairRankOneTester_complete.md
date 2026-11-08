<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticPairRankOneTester_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Rank-One Tester

**Claim.** For every γ, the rank-one tester accepts with probability 1 the oracle given by the dot product on vectors and the matrix character paired with the rank-one self-matrix of γ.

**Proof.** Use the acceptance-probability formula for the rank-one tester (quadraticPairRankOneTester_acceptanceProbability). For fixed x, y, and z, additivity of the matrix character in its matrix argument (binaryMatrixCharacter_add) rewrites the sum of the two matrix answers as twice the character of the reshaped z plus the character of the outer product x yᵀ. The character is the matrix pairing, and its value on an outer product is the corresponding rank-one pairing (binaryMatrixPairing_rankOne). For the rank-one self-matrix of γ, that pairing equals (γ·x)(γ·y) (matrixRankOnePairing_rankOneSelfMatrix). The two copies of the first matrix pairing cancel in characteristic two, leaving exactly (γ·x)(γ·y). Thus the acceptance condition holds for every triple, and the average of its constant-one indicator is 1.

**Key facts.** `FABL.quadraticPairRankOneTester_acceptanceProbability`, `FABL.binaryMatrixCharacter_add`, `FABL.binaryMatrixPairing_rankOne`, `FABL.matrixRankOnePairing_rankOneSelfMatrix`.
