<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean :: CommunicationComplexity.discrepancy_eq_prob_false_sub_prob_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Discrepancy as a probability difference

**Claim.** The discrepancy of a Boolean function on a set is the probability mass in that set where the function is false minus the probability mass there where it is true.

**Proof.** Write the false and true portions of the set as $S_{\mathrm{false}}$ and $S_{\mathrm{true}}$. The discrepancy integrand is the indicator of the set times the Boolean sign. Pointwise, this equals the indicator of $S_{\mathrm{false}}$ minus the indicator of $S_{\mathrm{true}}$ (`discrepancy_integrand_eq`): on the false portion the sign contributes $1$, on the true portion it contributes $-1$, and outside the set both indicators vanish. Integrating and using linearity turns the discrepancy into the difference of the two indicator integrals. Each indicator integral is the measure of its set (`FiniteProbabilitySpace.measureReal_eq_integral_indicator_one`), giving the stated difference of probabilities.

**Key facts.** `CommunicationComplexity.discrepancy_integrand_eq`, `CommunicationComplexity.FiniteProbabilitySpace.measureReal_eq_integral_indicator_one`.
