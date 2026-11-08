<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.abs_mul_thresholdSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute value times threshold sign

**Claim.** For every real number $r$, multiplying its absolute value by its threshold sign gives $r$.

**Proof.** If $r\ge0$, its threshold sign is $1$ and $|r|=r$, so the product is $r$. If $r<0$, its threshold sign is $-1$ and $|r|=-r$, again giving $r$.
