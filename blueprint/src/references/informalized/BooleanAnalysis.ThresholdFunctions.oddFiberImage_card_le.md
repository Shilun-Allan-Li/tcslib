<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.oddFiberImage_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-Fiber Image Cardinality Bound

**Claim.** For a map from $[n]$ to $[m]$ and a subset $S\subseteq[n]$, the set of target indices whose fibers inside $S$ have odd cardinality has size at most $|S|$.

**Proof.** Every target index with an odd-sized fiber has a nonempty fiber, so it lies in the image of $S$ under $\pi$. Thus the odd-fiber image is contained in $S\mathbin{.image}\pi$. Taking cardinalities gives the result, since the cardinality of an image cannot exceed that of its source.
