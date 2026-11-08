<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/Parameters.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_pos_lt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on the Bias Coefficient

**Claim.** For $1<p<2$ and $0<\alpha<\beta$, the bias coefficient lies strictly between $0$ and $1$.

**Proof.** By the hyperbolic-sine identity for the bias coefficient (`bias_coefficient_eq_sinh`), it equals
\[
\frac{\sinh\bigl((p-1)\log(\beta/\alpha)\bigr)}{\sinh\bigl(\log(\beta/\alpha)\bigr)}.
\]
Since $\beta/\alpha>1$, its logarithm is positive. Also $0<p-1<1$, so $(p-1)\log(\beta/\alpha)$ lies strictly between zero and $\log(\beta/\alpha)$. The hyperbolic sine is positive on positive arguments and strictly increasing; hence the numerator and denominator are positive, and the numerator is strictly smaller than the denominator. Their ratio is therefore strictly between zero and one.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_eq_sinh`.
