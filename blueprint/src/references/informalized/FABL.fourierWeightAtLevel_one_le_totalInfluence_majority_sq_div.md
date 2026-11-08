<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/ArrowLevelOneBound.lean :: FABL.fourierWeightAtLevel_one_le_totalInfluence_majority_sq_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Weight from Majority Influence

**Claim.** If all singleton Fourier coefficients of a Boolean function are equal and $n>0$, then its level-one Fourier weight is at most the square of majority's total influence divided by $n$.

**Proof.** Choose one coordinate $i$ and call its singleton coefficient $a$. Since all singleton coefficients agree, the level-one weight is $n a^2$ (`fourierWeightAtLevel_one_eq_sum_singleton`), while the sum of the singleton coefficients of the function is $na$. Majority is monotone, so its total influence equals the sum of its singleton Fourier coefficients (`totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone`, using `majority_monotone`). The comparison of singleton-coefficient sums with majority (`abs_sum_fourierCoeff_singleton_le_majority`) therefore gives $|na|\leq M$, where $M$ is majority's total influence. Since $M\geq0$ (`totalInfluence_nonneg`), squaring yields $(na)^2\leq M^2$. As $n>0$, divide by $n$ and use $(na)^2=n(na^2)$ to obtain the claim.

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.majority_monotone`, `FABL.totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone`, `FABL.abs_sum_fourierCoeff_singleton_le_majority`, `FABL.totalInfluence_nonneg`.
