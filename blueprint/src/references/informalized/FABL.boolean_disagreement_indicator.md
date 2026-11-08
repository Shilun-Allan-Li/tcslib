<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseOperator.lean :: FABL.boolean_disagreement_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Disagreement Indicator

**Claim.** For sign-valued outputs, the indicator that $f(x)$ and $f(y)$ disagree equals $(1-f(x)f(y))/2$, with the signs viewed as real numbers.

**Proof.** Each output is either $1$ or $-1$. If the outputs agree, their product is $1$, so the displayed expression is $0$ and the disagreement indicator is also $0$. If they differ, their product is $-1$, so the expression is $1$ and the indicator is also $1$. This verifies the identity in all cases.
