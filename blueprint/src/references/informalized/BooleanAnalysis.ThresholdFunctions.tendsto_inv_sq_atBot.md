<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_inv_sq_atBot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal-square decay

**Claim.** As $t\to-\infty$, $1/t^2$ tends to zero.

**Proof.** The square $t^2$ tends to $+\infty$ as $t\to-\infty$ (`tendsto_sq_atBot`). Taking reciprocals therefore gives a limit of zero, by the reciprocal map’s limit at positive infinity.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.tendsto_sq_atBot`.
