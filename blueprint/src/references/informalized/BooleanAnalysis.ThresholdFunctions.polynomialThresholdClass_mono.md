<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.polynomialThresholdClass_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Polynomial Threshold Classes

**Claim.** If $k\leq k'$, every $\{-1,1\}$-valued function with a polynomial threshold representation of degree at most $k$ also has one of degree at most $k'$.

**Proof.** Keep the same representing polynomial. Any index set of size greater than $k'$ also has size greater than $k$, so its coefficient already vanishes by the degree-at-most-$k$ condition. The polynomial therefore has degree at most $k'$, while its threshold representation and the function's Boolean-valued property are unchanged.
