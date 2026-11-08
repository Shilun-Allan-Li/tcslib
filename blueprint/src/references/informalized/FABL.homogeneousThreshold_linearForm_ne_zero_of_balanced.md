<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.homogeneousThreshold_linearForm_ne_zero_of_balanced -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonvanishing of a Balanced Threshold Form

**Claim.** If a Boolean function is balanced and agrees everywhere with the threshold sign of a linear form, then that linear form is nonzero at every sign vector.

**Proof.** Pair each sign vector $x$ with its negation $-x$. The linear form changes sign under this negation (\texttt{linearForm\_neg\_input\_regularThreshold}). If its value at $x$ is nonzero, the two threshold signs are opposites (\texttt{thresholdSign\_neg}); if it is zero, both threshold signs are $1$. Since the function agrees with these threshold signs, the sum of its real values at $x$ and $-x$ is therefore $0$ in the nonzero case and $2$ in the zero case. In particular this sum is pointwise nonnegative. Negation permutes the uniform sign cube, so the expectation of the function at $-x$ equals its expectation at $x$; balance makes both expectations zero. The expectation of the paired sum is thus zero. A nonnegative function on a finite uniform space with expectation zero vanishes at every point, so the paired sum is zero everywhere. It cannot equal $2$, and hence the linear form never vanishes.

**Key facts.** `FABL.linearForm_neg_input_regularThreshold`, `FABL.thresholdSign_neg`.
