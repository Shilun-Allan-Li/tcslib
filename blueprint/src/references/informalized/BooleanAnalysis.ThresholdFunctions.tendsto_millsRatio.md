<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_millsRatio -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mills ratio limit

**Claim.** The standard Gaussian Mills ratio tends to $1$ as $t\to-\infty$.

**Proof.** For negative $t$, the Mills ratio lies between $1-1/t^2$ and $1$: the lower bound is `one_sub_le_millsRatio`, and the upper bound is `millsRatio_le_one`. Since $1/t^2\to0$ (`tendsto_inv_sq_atBot`), the lower bound tends to $1$, while the upper bound is constantly $1$. The squeeze theorem gives the asserted limit.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.tendsto_inv_sq_atBot`, `BooleanAnalysis.ThresholdFunctions.one_sub_le_millsRatio`, `BooleanAnalysis.ThresholdFunctions.millsRatio_le_one`.

**Caveat.** The supplied informal statement describes a different asymptotic claim; this account follows the formal statement and proof, which establish the Mills ratio limit.
