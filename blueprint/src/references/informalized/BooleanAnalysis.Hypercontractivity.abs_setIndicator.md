<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.abs_setIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Value of a Set Indicator

**Claim.** For a finite subset of the Boolean cube, the absolute value of its indicator at any point equals the indicator itself.

**Proof.** The indicator is nonnegative (setIndicator_nonneg). The absolute value of any nonnegative real number is that number, so the equality follows pointwise.

**Key facts.** `BooleanAnalysis.Hypercontractivity.setIndicator_nonneg`.
