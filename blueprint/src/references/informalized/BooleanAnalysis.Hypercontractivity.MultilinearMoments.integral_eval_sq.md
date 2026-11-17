<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Moments.lean :: BooleanAnalysis.Hypercontractivity.MultilinearMoments.integral_eval_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second moment of a multilinear polynomial

**Claim.** For independent centered random variables with unit second moments and finite fourth moments, the second moment of the multilinear polynomial evaluation is the sum of the squares of its coefficients.

**Proof.** Apply the bilinear moment identity (`MultilinearMoments.integral_eval_mul`) with both coefficient functions equal to $F$. It gives the integral of the product of the two evaluations as $\sum_S F(S)F(S)$. The product is the square of the evaluation, and each summand is $F(S)^2$, yielding the claimed equality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.MultilinearMoments.integral_eval_mul`.
