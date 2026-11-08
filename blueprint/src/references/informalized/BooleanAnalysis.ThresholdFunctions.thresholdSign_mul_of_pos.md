<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.thresholdSign_mul_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Scaling Preserves Threshold Sign

**Claim.** For $c>0$, the threshold sign of $cr$ equals the threshold sign of $r$.

**Proof.** Because $c$ is positive, multiplication by $c$ preserves the sign of $r$: if $r\ge0$, then $cr\ge0$; conversely, if $cr\ge0$, division of this inequality by the positive number $c$ gives $r\ge0$. Thus the conditions that select the value $1$ in the two threshold signs are equivalent, so the threshold signs agree.
