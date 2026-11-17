<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.expect_centeredLinearSquare_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second moment of the centered linear square

**Claim.** For a linear form on the sign cube, half the average of its centered square is the square of the sum of squared coefficients minus the sum of their fourth powers.

**Proof.** The centered linear square is the random variable $L^2-\sum_i a_i^2$. Its mean is zero because $\mathbb E L^2=\sum_i a_i^2$ (`expect_linearForm_sq`). Consequently its second moment is the variance of $L^2$. The variance identity for the squared linear form states that this variance divided by $2$ is $(\sum_i a_i^2)^2-\sum_i a_i^4$ (`variance_linearForm_sq`), as required.

**Key facts.** `FABL.variance_linearForm_sq`, `FABL.expect_linearForm_sq`.
