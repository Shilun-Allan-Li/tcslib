<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.inv_two_pow_eq_four_mul_juntaConstantAccuracy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accuracy parameter and inverse power identity

**Claim.** For every natural number $k$, the inverse power $(1/2)^k$ equals four times the first coordinate of the learning parameter defined from $k$.

**Proof.** Use the stated formula for the real-valued first coordinate of the learning parameter (`juntaConstantAccuracy_cast`), namely $2^{-(k+2)}$. Then $(1/2)^k=2^{-k}$, while four times that coordinate is $4\cdot2^{-(k+2)}=2^{-k}$. The two expressions are therefore equal.

**Key facts.** `FABL.juntaConstantAccuracy_cast`.
