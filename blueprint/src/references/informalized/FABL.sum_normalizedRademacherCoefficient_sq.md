<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.sum_normalizedRademacherCoefficient_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Coefficient Normalization

**Claim.** For every natural number $m$, the sum over $m+1$ coordinates of the squares of the coefficient $1/\sqrt{m+1}$ is $1$.

**Proof.** There are exactly $m+1$ terms in the sum, each equal to the square of the reciprocal square root of $m+1$. Thus the sum is $(m+1)/\bigl(\sqrt{m+1}\bigr)^2$. Since $m+1>0$, its square root squares to $m+1$, and the quotient is $1$.
