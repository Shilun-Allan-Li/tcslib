<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticSystemProofFunctionTester_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Quadratic-System Tester

**Claim.** If $w$ satisfies every equation in $L$, then the proof encoding the truth tables of its linear character and rank-one matrix character makes the quadratic-system proof tester accept with probability one.

**Proof.** Apply the acceptance-probability identity to replace the four-query tester’s acceptance probability by that of the linearized-system character tester on the function read from the proof table (`quadraticSystemProofFunctionTester_acceptanceProbability`). The specified proof encoding makes this matrix function the character of the rank-one matrix $ww^{\mathsf T}$ (`quadraticMatrixProofFunction_encodeHomogeneousQuadraticProof`). At a matrix-cube point, the character of a matrix evaluated on the unflattened point equals the dot product of its flattened matrix with that point (`binaryMatrixCharacter_unflattenBinaryMatrix`). Consequently the proof supplies exactly the linear character function required by the linearized-system tester, with parameter the flattening of $ww^{\mathsf T}$. Since $w$ satisfies the original quadratic system, the rank-one characterization says this parameter satisfies the linearized system (`satisfiesLinearized_rankOne_iff`). The completeness theorem for the character tester therefore gives acceptance probability one (`linearizedQuadraticSystemCharacterTester_complete`).

**Key facts.** `FABL.quadraticSystemProofFunctionTester_acceptanceProbability`, `FABL.quadraticMatrixProofFunction_encodeHomogeneousQuadraticProof`, `FABL.binaryMatrixCharacter_unflattenBinaryMatrix`, `FABL.satisfiesLinearized_rankOne_iff`, `FABL.linearizedQuadraticSystemCharacterTester_complete`.
