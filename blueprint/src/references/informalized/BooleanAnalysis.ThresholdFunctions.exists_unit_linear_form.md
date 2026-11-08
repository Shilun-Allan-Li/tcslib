<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/DegreeOne.lean :: BooleanAnalysis.ThresholdFunctions.exists_unit_linear_form -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unit linear form with prescribed correlation

**Claim.** If the level-one Fourier weight of $g$ is positive, there are coefficients of squared norm one whose linear form has correlation with $g$ equal to the square root of that weight.

**Proof.** Write $c_i=\widehat g(\{i\})$ and set $a_i=c_i/\sqrt{W_1[g]}$. Positivity of the weight makes the denominator positive, and the identity expressing level-one weight as the sum of squared singleton coefficients (`weightLevel_one_eq_sum_singleton`) gives $\sum_i a_i^2=W_1[g]/W_1[g]=1$. The expected product of $g$ with a linear form having coefficients $a_i$ is $\sum_i a_i\widehat g(\{i\})$ by the expectation formula (`expect_mul_linear_form`). Substituting the chosen coefficients makes this sum $\sum_i c_i^2/\sqrt{W_1[g]}=W_1[g]/\sqrt{W_1[g]}=\sqrt{W_1[g]}$, as required.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_mul_linear_form`, `BooleanAnalysis.ThresholdFunctions.weightLevel_one_eq_sum_singleton`.
