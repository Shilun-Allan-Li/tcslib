<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/NearlyConstantLevelOne.lean :: FABL.mean_nearlyConstantMinorityIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Minority Indicator

**Claim.** The uniform mean of the nearly constant minority indicator is \(\bigl(1-|\mathbb E f|\bigr)/2\), where the mean of \(f\) is taken after viewing its values as real numbers.

**Proof.** Split according to the sign of the mean of \(f\). If the mean is nonnegative, the indicator is pointwise \((1-f)/2\). Linearity of expectation and the fact that the expectation of a constant is that constant give its mean as \((1-\mathbb E f)/2\). In this case \(|\mathbb E f|=\mathbb E f\), proving the formula. If the mean is negative, the indicator is \((1+f)/2\), so the same expectation rules give mean \((1+\mathbb E f)/2\). Now \(|\mathbb E f|=-\mathbb E f\), and this is again \((1-|\mathbb E f|)/2\).
