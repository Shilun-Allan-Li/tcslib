<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.kane_totalInfluence_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Influence Bound for Polynomial Thresholds

**Claim.** There is a positive constant $C$ such that every function in the degree-$k$ polynomial threshold class on the $n$-dimensional cube has total influence at most $\sqrt n\,\operatorname{rpow}(2^k\log(\max\{n,2\}),Ck\log(\max\{k,2\}))$.

**Proof.** Choose the positive constant and the degree-at-least-two estimate from `kane_totalInfluence_bound_of_two_le`. If $k\ge2$, that estimate applies directly. If $k<2$, then $k\le1$. The degree-reduction result (`isLinearThreshold_of_polynomialThresholdClass`) makes the function a linear threshold, and the linear-threshold influence estimate (`ltf_totalInfluence_le_sqrt`) bounds its total influence by $\sqrt n$. In this low-degree case the real-power factor in the claimed bound is at least one: its base is at least one, and its exponent is nonnegative. Hence $\sqrt n$ is at most the claimed right-hand side, completing both cases.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.kane_totalInfluence_bound_of_two_le`, `BooleanAnalysis.ThresholdFunctions.isLinearThreshold_of_polynomialThresholdClass`, `BooleanAnalysis.ThresholdFunctions.ltf_totalInfluence_le_sqrt`.
