<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.runWithCost_seededMatrixProductVerificationAfterSeed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seeded Verification Cost After Fixing the Seed

**Claim.** Once the seed bits are fixed, the verification program returns the seeded matrix-product verification result deterministically and has cost $(0,0,6n^2+4n+1)$.

**Proof.** The program first incurs a tick of the matrix-product verification work and then returns the verification result as a pure value. Running a pure return gives that value with zero additional cost; the tick adds $(0,0,6n^2+4n+1)$. Hence the run is the point mass at the stated output and cost.
