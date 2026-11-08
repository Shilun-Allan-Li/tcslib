<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.cubeLpNorm_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering the absolute moment

**Claim.** For $q>0$, the $q$th power of the Boolean-cube power mean of $f$ equals the expectation of $|f|^q$.

**Proof.** The expectation of $|f|^q$ is nonnegative, since each integrand is nonnegative and the expectation preserves nonnegativity. By definition, the power mean is this expectation raised to $1/q$. The real-power multiplication law therefore gives its $q$th power as the expectation raised to $(1/q)q=1$, which is the expectation itself.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_nonneg`.
