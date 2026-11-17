<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/AffineKhintchine.lean :: BooleanAnalysis.ThresholdFunctions.influence_abs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute values decrease influence

**Claim.** For every real-valued function on the Boolean cube and every coordinate, the influence of its pointwise absolute value is at most the influence of the original function.

**Proof.** At each point, the reverse triangle inequality gives $\bigl||h(x)|-|h(x^{i})|\bigr|\le |h(x)-h(x^{i})|$, where $x^{i}$ is $x$ with coordinate $i$ flipped. Squaring preserves this inequality because both sides are nonnegative; dividing by $4$ gives the pointwise comparison of the quantities averaged in the influence. Monotonicity of expectation (`expect_mono`) then gives the asserted influence bound.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_mono`.
