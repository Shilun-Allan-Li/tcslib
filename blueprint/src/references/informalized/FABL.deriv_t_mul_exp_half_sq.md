<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ContinuousReasonableness.lean :: FABL.deriv_t_mul_exp_half_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Gaussian exponential function

**Claim.** For every real $t$, the derivative of $t e^{t^2/2}$ is $(1+t^2)e^{t^2/2}$.

**Proof.** Fix $t$ and differentiate the product $t e^{t^2/2}$. The derivative of the first factor is $1$, while the derivative of the second is $t e^{t^2/2}$ by the Gaussian exponential derivative formula ($\texttt{FABL.deriv\_exp\_half\_sq}$). The product rule therefore gives $e^{t^2/2}+t^2e^{t^2/2}=(1+t^2)e^{t^2/2}$.

**Key facts.** `FABL.deriv_exp_half_sq`.
