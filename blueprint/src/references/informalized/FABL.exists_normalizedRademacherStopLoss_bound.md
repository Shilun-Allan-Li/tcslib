<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.exists_normalizedRademacherStopLoss_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized Rademacher Stop-Loss Bound

**Claim.** A universal positive constant bounds, uniformly in $m$ and $t$, the discrepancy between the normalized Rademacher sum stop-loss expectation and the standard Gaussian stop-loss value by that constant times $1/\sqrt{m+1}$.

**Proof.** Use the uniform stop-loss estimate for regular linear forms (`exists_stopLoss_linearForm_sub_standardGaussian_le_of_regular`) with every coefficient equal to the normalized Rademacher coefficient for $m+1$ signs. The squared coefficients sum to one (`sum_normalizedRademacherCoefficient_sq`), and each coefficient's absolute value is bounded by that coefficient because it is nonnegative (`normalizedRademacherCoefficient_nonneg`). For $t\ge0$, the estimate applies directly and its linear form is the normalized Rademacher sum. For $t<0$, apply the same estimate at $-t\ge0$. Reflection identities for the Rademacher expectation and Gaussian stop-loss (`expect_normalizedRademacherStopLoss_reflection`, `standardGaussianStopLoss_reflection`) add the same term $-t$ to both quantities, so their difference in absolute value is unchanged. The same constant therefore works for every real threshold.

**Key facts.** `FABL.exists_stopLoss_linearForm_sub_standardGaussian_le_of_regular`, `FABL.sum_normalizedRademacherCoefficient_sq`, `FABL.normalizedRademacherCoefficient_nonneg`, `FABL.expect_normalizedRademacherStopLoss_reflection`, `FABL.standardGaussianStopLoss_reflection`.
