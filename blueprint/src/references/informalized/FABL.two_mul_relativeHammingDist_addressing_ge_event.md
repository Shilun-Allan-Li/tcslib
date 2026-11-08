<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.two_mul_relativeHammingDist_addressing_ge_event -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addressing function error bound

**Claim.** If \(g\) depends only on coordinates in \(J\), then the probability that the addressing function selects a coordinate outside \(J\) is at most twice the relative Hamming distance between the addressing function and \(g\).

**Proof.** The proof first uses the counting estimate that twice the total addressing error-indicator sum is at least the number of inputs whose selected coordinate lies outside \(J\) (\(\texttt{FABL.two_mul_sum_addressingErrorIndicator_ge_event_card}\)). Convert both sides to uniform probabilities: the probability of disagreement between two functions on a finite uniform domain equals their relative Hamming distance (\(\texttt{FABL.uniformProbability_ne_eq_relativeHammingDist}\)). Both quantities are therefore counts divided by the cardinality of the input cube. That cardinality is positive, so multiplying through by it preserves the inequality; the result is the stated probability bound.

**Key facts.** `FABL.two_mul_sum_addressingErrorIndicator_ge_event_card`, `FABL.uniformProbability_ne_eq_relativeHammingDist`.
