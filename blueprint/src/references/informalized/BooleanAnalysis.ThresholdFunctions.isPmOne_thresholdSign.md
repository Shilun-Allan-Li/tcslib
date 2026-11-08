<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.isPmOne_thresholdSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Signs Are Unit-Valued

**Claim.** Applying the threshold sign to any real-valued function on the Boolean cube gives a function taking only the values $1$ and $-1$.

**Proof.** Fix any cube point $x$. The threshold sign of the real number $g(x)$ is either $1$ or $-1$ (`thresholdSign_pm_one`). Since this holds at every point, the resulting function is unit-valued.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.thresholdSign_pm_one`.
