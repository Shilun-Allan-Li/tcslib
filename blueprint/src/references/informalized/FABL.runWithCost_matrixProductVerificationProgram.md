<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.runWithCost_matrixProductVerificationProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix verification run law

**Claim.** The matrix product verification program has the law of a uniform random bit vector paired with the verification decision on its corresponding vector in $\mathbb F_2^n$, with cost $(0,0,n+6n^2+4n+1)$, independently of the Boolean function.

**Proof.** Apply the seeded verification run-law theorem to the seed that converts a length-$n$ bit vector into its corresponding vector in $\mathbb F_2^n$ (the fact that a bit vector is uniform is preserved by this coordinatewise correspondence). That theorem says the run law is uniform on the seed bits, mapped to the seeded verification result and the cost $(0,0,n+6n^2+4n+1)$. Unfolding the definitions of the matrix verification program, its random-bit count, and its cost gives exactly the claimed expression; the target function plays no role in this program.

**Key facts.** `FABL.runWithCost_seededMatrixProductVerificationProgram`.
