<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/NearlyConstantLevelOne.lean :: FABL.mean_nearlyConstantMinorityIndicator_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Minority Indicator Mean

**Claim.** For a Boolean function on the sign cube, the uniform mean of its nearly constant minority indicator is nonnegative.

**Proof.** The exact formula for the indicator's mean (\(\texttt{FABL.mean_nearlyConstantMinorityIndicator}\)) expresses it as \((1-|\mathbb E f|)/2\). The bound \(|\mathbb E f|\le 1\) for a real-valued sign function (\(\texttt{FABL.abs_mean_toReal_le_one}\)) makes the numerator nonnegative, and division by \(2\) preserves that inequality.

**Key facts.** `FABL.mean_nearlyConstantMinorityIndicator`, `FABL.abs_mean_toReal_le_one`.
