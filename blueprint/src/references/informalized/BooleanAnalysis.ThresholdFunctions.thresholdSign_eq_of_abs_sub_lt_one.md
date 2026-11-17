<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.thresholdSign_eq_of_abs_sub_lt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Sign Stability

**Claim.** If $y$ is either $1$ or $-1$ and $|y-r|<1$, then the threshold sign of $r$ is $y$.

**Proof.** The absolute value bound gives $-1<y-r<1$. If $y=1$, the lower bound yields $r>0$, so $r$ is nonnegative and its threshold sign is $1$ (`thresholdSign_of_nonneg`). If $y=-1$, the upper bound yields $r<0$, so its threshold sign is $-1$ (`thresholdSign_of_neg`). In either case the sign equals $y$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.thresholdSign_of_nonneg`, `BooleanAnalysis.ThresholdFunctions.thresholdSign_of_neg`.
