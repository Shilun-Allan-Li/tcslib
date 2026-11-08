<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.expect_abs_indicator_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moment of an Indicator

**Claim.** For a finite subset $A$ of the Boolean cube and $r>0$, the expectation of the $r$th power of the absolute value of its indicator equals the volume of $A$.

**Proof.** By definition, the volume of $A$ is the expectation of its indicator. At each point of the cube, the indicator is either $0$ or $1$, so its absolute value raised to a positive power equals the indicator itself (\texttt{abs\_setIndicator\_rpow}). Thus the two functions inside the expectations agree pointwise, and their expectations are equal.

**Key facts.** `BooleanAnalysis.Hypercontractivity.abs_setIndicator_rpow`.
