<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Moments.lean :: BooleanAnalysis.Hypercontractivity.MultilinearMoments.eval_supported -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation on a Supported Coordinate Set

**Claim.** If all coefficients indexed by sets not contained in $s$ vanish, the multilinear evaluation equals the sum restricted to subsets of $s$.

**Proof.** The full evaluation sums over every subset $T$ of the coordinate set. Restrict this sum to the subsets of $s$, which form a subfamily. Every omitted term has $T\not\subseteq s$, so its coefficient is zero by hypothesis and its contribution vanishes. The full sum therefore equals the sum over the subsets of $s$.
