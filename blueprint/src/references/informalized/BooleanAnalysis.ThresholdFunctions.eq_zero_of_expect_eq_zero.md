<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.eq_zero_of_expect_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero average forces pointwise vanishing

**Claim.** A pointwise nonnegative function on the Boolean cube whose uniform expectation is zero vanishes at every point.

**Proof.** Rewrite the uniform expectation as the finite uniform expectation over the Boolean cube (`expect_eq_fintypeExpect`). For a nonnegative function on a finite probability space, expectation zero is equivalent to pointwise vanishing, by the finite expectation zero criterion (`Fintype.expect_eq_zero_iff_of_nonneg`). Applying that criterion gives the claimed equality of functions.

**Key facts.** `BooleanAnalysis.expect_eq_fintypeExpect`.
