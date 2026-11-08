<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.indicator_Lr_norm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Moment Norm

**Claim.** For a finite subset $A$ of the Boolean cube and $r>0$, the $r$-moment norm of its indicator equals $\operatorname{volume}(A)^{1/r}$.

**Proof.** The expectation of the $r$th power of the absolute value of the indicator equals the volume of $A$ (`expect_abs_indicator_rpow`). Raising both sides of that equality to the power $1/r$ gives the stated identity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.expect_abs_indicator_rpow`.
