<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.tendsto_normalizedRademacherCoefficient_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing normalized coefficient

**Claim.** As \(m\to\infty\), the sequence \((m+1)^{-1/2}\) tends to zero.

**Proof.** The natural numbers tend to infinity, and taking their real square roots preserves divergence to infinity. The reciprocals of a sequence tending to positive infinity converge to zero, so the normalized coefficient tends to zero. Composing this limit with the shift \(m\mapsto m+1\), which also tends to infinity, gives the stated result.
