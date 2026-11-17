<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.expect_eq_zero_of_flipCoordinate_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Antisymmetric Average Vanishes

**Claim.** If flipping coordinate $i$ negates $q$ at every point of the sign cube, then the uniform average of $q$ is zero.

**Proof.** Flipping coordinate $i$ is a bijection of the sign cube, so changing variables by this bijection leaves the uniform average unchanged. By the hypothesis, the resulting average is also the average of $-q$, which equals the negative of the average of $q$. Thus the average equals its own negative, and hence is zero.
