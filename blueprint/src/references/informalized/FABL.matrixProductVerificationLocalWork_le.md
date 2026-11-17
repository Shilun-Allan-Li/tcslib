<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductVerificationLocalWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local verification work bound

**Claim.** For every natural number $n$, the quantity $6n^2+4n+1$ is at most $11(n+1)^2$.

**Proof.** Expanding the right-hand side and subtracting the left gives $11(n+1)^2-(6n^2+4n+1)=5n^2+18n+10$, which is nonnegative for every natural number $n$. Hence the stated inequality holds.
