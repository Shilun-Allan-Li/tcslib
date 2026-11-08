<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.abs_setIndicator_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Powers of a Set Indicator

**Claim.** For a finite subset of the Boolean cube and any positive real exponent, the exponentiated absolute value of its indicator equals the indicator.

**Proof.** First replace the absolute value by the indicator itself using its nonnegativity, as established by the absolute-value identity (abs_setIndicator). Then apply the fact that a positive power of the indicator equals the indicator (setIndicator_rpow), valid because the exponent is positive.

**Key facts.** `BooleanAnalysis.Hypercontractivity.abs_setIndicator`, `BooleanAnalysis.Hypercontractivity.setIndicator_rpow`.
