<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.ConditionalExpectationPolytimeAdapter.decoded_output_correct_and_work_le_polynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional expectation adapter guarantees

**Claim.** For every encoded input, the adapter’s output decodes to the packed assignment from its conditional-expectation plan; that assignment’s CSP value is at least the randomized assignment’s expected value, and the plan’s work is bounded by the stated polynomial.

**Proof.** Apply the adapter’s output-and-value guarantee (FABL.ConditionalExpectationPolytimeAdapter.decoded_output_value_ge_expected) to the input. It gives the decoding identity and the comparison between expected value and the plan assignment’s value. Separately, apply the plan’s work bound (FABL.FiniteRandomizedCSPInput.conditionalExpectationPlan_work_le_polynomial) to the semantic input; this bounds its work by the conditional-expectation work polynomial evaluated at the sum of the variable and constraint counts. Pair these two conclusions to obtain the result.

**Key facts.** `FABL.ConditionalExpectationPolytimeAdapter.decoded_output_value_ge_expected`, `FABL.FiniteRandomizedCSPInput.conditionalExpectationPlan_work_le_polynomial`.
