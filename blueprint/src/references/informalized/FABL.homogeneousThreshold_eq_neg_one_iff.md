<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.homogeneousThreshold_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Threshold Characterization

**Claim.** If a Boolean function equals the threshold sign of a linear form at every sign vector, then its value is $-1$ exactly where that linear form is negative.

**Proof.** For the forward implication, replace the function value by its threshold representation. If the linear form were nonnegative, the threshold sign would be $1$ by the nonnegative-threshold rule (\texttt{thresholdSign\_of\_nonneg}), contradicting that the value is $-1$. For the reverse implication, a negative linear form has threshold sign $-1$ by the negative-threshold rule (\texttt{thresholdSign\_of\_neg}); the representation hypothesis then gives the stated value.

**Key facts.** `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
