<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.thresholdSign_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Threshold Sign

**Claim.** If $r\le s$, then the threshold sign of $r$ is at most the threshold sign of $s$.

**Proof.** If $r\ge0$, then also $s\ge0$, so both threshold signs equal $1` by the nonnegative-input rule (`thresholdSign_of_nonneg`). If instead $r<0$, its threshold sign is $-1$ (`thresholdSign_of_neg`). The threshold sign of $s$ is either $1$ or $-1$ (`thresholdSign_pm_one`), and in either case it is at least $-1$. Thus the desired inequality holds.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.thresholdSign_of_nonneg`, `BooleanAnalysis.ThresholdFunctions.thresholdSign_of_neg`, `BooleanAnalysis.ThresholdFunctions.thresholdSign_pm_one`.
