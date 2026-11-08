<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceDistribution.lean :: BooleanAnalysis.GaussianSpace.Invariance.levyDistance_le_of_cdf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CDF bounds control Lévy distance

**Claim.** If the two stated CDF inequalities hold with a nonnegative parameter $\epsilon$ at every real threshold, then the Lévy distance from $\mu$ to $\nu$ is at most $\epsilon$.

**Proof.** The parameter $\epsilon$ belongs to the set whose infimum defines the Lévy distance: it is nonnegative by hypothesis, and its required pair of CDF inequalities is exactly the assumed condition. The infimum of a set is at most each member of that set, so the Lévy distance is at most $\epsilon$.
