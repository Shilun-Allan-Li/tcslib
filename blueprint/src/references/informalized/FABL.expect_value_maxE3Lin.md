<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.expect_value_maxE3Lin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Value of a Three-Variable Linear System

**Claim.** For the stated instance of three-variable linear constraints over $\mathbb F_2$, the expected fraction of satisfied constraints under a uniformly random assignment is $1/2$.

**Proof.** Write the value as the total number of satisfied constraints divided by the number of constraints, and move this fixed denominator outside the expectation. The expected total satisfied count is the expected sum of the satisfaction indicators over the constraint multiset. The supplied fact that this expected sum is half the number of constraints (`expect_satisfiedIndicators_maxE3Lin`) therefore gives an expected numerator equal to half the denominator. The denominator is nonzero because the constraint multiset is nonempty, so division yields $1/2$.

**Key facts.** `FABL.expect_satisfiedIndicators_maxE3Lin`.
