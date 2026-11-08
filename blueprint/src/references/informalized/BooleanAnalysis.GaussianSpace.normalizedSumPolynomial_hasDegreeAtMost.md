<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/NormalizedSums.lean :: BooleanAnalysis.GaussianSpace.normalizedSumPolynomial_hasDegreeAtMost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for the normalized sum

**Claim.** For every nonnegative integer $n$, the multilinear coefficient family supported on singleton subsets has degree at most one, with coefficient $1/\sqrt n$ there and zero elsewhere.

**Proof.** To verify degree at most one, take any subset $S$ with more than one element. Its cardinality is not one, so the defining coefficient of the normalized-sum polynomial is the zero branch. Thus every coefficient indexed by a set of cardinality greater than one vanishes, which is exactly the required degree bound. This also covers $n=0$, when there are no singleton subsets.
