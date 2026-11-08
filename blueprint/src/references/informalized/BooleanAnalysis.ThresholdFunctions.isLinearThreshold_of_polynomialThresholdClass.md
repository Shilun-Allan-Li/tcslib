<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.isLinearThreshold_of_polynomialThresholdClass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree At Most One Thresholds

**Claim.** If a function belongs to the polynomial threshold class of degree at most $k$, where $k\le1$, then it is a linear threshold function.

**Proof.** Membership supplies a polynomial threshold representation of the function by some polynomial $p$ of degree at most $k$. For any set of variables whose size exceeds one, its size also exceeds $k$, since $k\le1$. The degree bound on $p$ therefore makes its coefficient vanish on every such set, which is precisely the degree-at-most-one condition. The same polynomial and threshold representation then witness that the function is a linear threshold.
