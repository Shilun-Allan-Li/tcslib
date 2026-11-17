<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.affinePoly_hasDegreeAtMost_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Bound for Affine Coefficients

**Claim.** For $n\in\mathbb N$, $c\in\mathbb R$, and $a\in\mathbb R^n$, the affine coefficient family has degree at most one: its coefficient at every subset $S$ with $|S|>1$ is zero.

**Proof.** Fix a subset $S$ with $|S|>1$. It is nonempty, so the constant-coefficient branch does not apply. Also, it cannot be a singleton, since that would give $|S|=1$. Therefore, for every coordinate $i$, the condition $S=\{i\}$ fails, and every term in the defining sum is zero. Hence the coefficient at $S$ is zero.
