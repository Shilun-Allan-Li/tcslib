<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ContinuousReasonableness.lean :: FABL.deriv_exp_half_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of an exponential quadratic

**Claim.** For every real $t$, the derivative of $t\mapsto \exp(t^2/2)$ is $t\exp(t^2/2)$.

**Proof.** The chain rule gives the derivative as $\exp(t^2/2)$ times the derivative of $t^2/2$. The latter derivative is $t$, by the power rule and division by the constant $2$. Thus the derivative is $t\exp(t^2/2)$.
