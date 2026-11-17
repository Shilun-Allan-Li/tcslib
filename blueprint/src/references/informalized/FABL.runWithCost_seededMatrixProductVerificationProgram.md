<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.runWithCost_seededMatrixProductVerificationProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distribution and Cost of Seeded Verification

**Claim.** The seeded verification program draws a uniform length-$r$ Boolean vector and returns the corresponding seeded matrix-product verification result with cost $(0,0,r+6n^2+4n+1)$.

**Proof.** Unfold the seeded program as a bind: it first runs the random-bit-vector program, then performs the verification tick and returns the result for the sampled bits. The random-bit-vector run is uniform over length-$r$ Boolean vectors and costs $(0,0,r)$ ( `runWithCost_randomBitVectorProgram`). The bind rule combines this law with the continuation’s run while adding the first-stage cost ( `LearningProgram.runWithCost_bind`). For each fixed bit vector, the continuation returns the seeded verification result deterministically and costs $(0,0,6n^2+4n+1)$ ( `runWithCost_seededMatrixProductVerificationAfterSeed`). Adding these costs gives $(0,0,r+6n^2+4n+1)$, which is the defined matrix-product verification cost ( `matrixProductVerificationCost_eq`).

**Key facts.** `FABL.LearningProgram.runWithCost_bind`, `FABL.runWithCost_randomBitVectorProgram`, `FABL.runWithCost_seededMatrixProductVerificationAfterSeed`, `FABL.matrixProductVerificationCost_eq`.
