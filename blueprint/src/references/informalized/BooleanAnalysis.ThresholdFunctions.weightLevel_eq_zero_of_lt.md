<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Majority.lean :: BooleanAnalysis.ThresholdFunctions.weightLevel_eq_zero_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier weights above dimension

**Claim.** If $n<k$, then the Fourier weight of any function on $\{0,1\}^n$ at level $k$ is zero.

**Proof.** Every subset $S$ of the $n$ coordinates has cardinality at most $n$. Since $n<k$, no such set has cardinality $k$. Thus each summand defining the level-$k$ weight takes its zero branch, and the entire sum is zero.
