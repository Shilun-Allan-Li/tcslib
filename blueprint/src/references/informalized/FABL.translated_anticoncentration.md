<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveAnticoncentration.lean :: FABL.translated_anticoncentration -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Translated Anticoncentration Bound

**Claim.** Under the stated mean-zero, positive norm, and hypercontractivity hypotheses, the probability that $|X-\theta|$ exceeds $t\|X\|_2$ is at least $(1-t^2)^2\rho^4$.

**Proof.** Apply the exact translated anticoncentration bound (`translated_anticoncentration_exact`). Put $u=(\theta/\|X\|_2)^2$ and $A=1-t^2$. The hypotheses on $t$ give $A\geq0$, while $u\geq0$; also $0<\rho\leq1$. These inequalities imply $\rho^2 A\leq(\rho^2 A+\rho^2u)/(1+\rho^2u)$: after multiplying by the positive denominator, the needed inequality reduces to $\rho^4Au\leq\rho^2u$, which follows from $\rho^2A\leq1$. Both sides are nonnegative, so squaring preserves the inequality. The square of the left side is $(1-t^2)^2\rho^4$, and the square of the right side is the lower bound supplied by the exact theorem. Combining them yields the stated estimate.

**Key facts.** `FABL.translated_anticoncentration_exact`.
